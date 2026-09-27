#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for release enumeration and checkout metadata boundaries."""
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import os
import unittest
from unittest.mock import patch

import build_release_manifest as release
import verify_snapshot as snapshot
import check_axiom_budget as axioms


class ReleaseToolsTests(unittest.TestCase):
    def test_publication_inventory_is_every_paper_order_entry_and_refuses_a_stray(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(axioms, "REPO_ROOT", Path(tmp)):
            root = Path(tmp)
            for number in axioms.PALOMAR_PROBLEMS:
                for index in (1, 2):
                    entry = root / f"PalomarCorpus/E{number}_{index:02d}"
                    entry.mkdir(parents=True)
                    (entry / "comparator.json").write_text("{}")
            found = axioms.entries(palomar=True)
            self.assertEqual(len(found), 16)
            self.assertEqual(found[:3], ["PalomarCorpus/E68_01", "PalomarCorpus/E68_02", "PalomarCorpus/E243_01"])
            extra = root / "PalomarCorpus/E70_01"
            extra.mkdir()
            (extra / "comparator.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "unrecognised"):
                axioms.entries(palomar=True)

    def test_publication_inventory_still_reads_a_problem_and_band_tree(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(axioms, "REPO_ROOT", Path(tmp)):
            root = Path(tmp)
            for name in [f"E{number}" for number in axioms.PALOMAR_PROBLEMS] + ["E257a"]:
                entry = root / f"PalomarCorpus/{name}"
                entry.mkdir(parents=True)
                (entry / "comparator.json").write_text("{}")
            # Bands were never audited while the inventory demanded exactly the eight.
            self.assertIn("PalomarCorpus/E257a", axioms.entries(palomar=True))
            (root / "PalomarCorpus/comparator.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "flat"):
                axioms.entries(palomar=True)

    def test_publication_audit_rejects_candidate_local_challenge_import(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(axioms, "REPO_ROOT", Path(tmp)), \
                patch.object(axioms, "source_identity", return_value={"commit": "test"}):
            entry = Path(tmp) / "PalomarCorpus/E68"
            entry.mkdir(parents=True)
            (entry / "comparator.json").write_text(json.dumps({
                "challenge_module": "PalomarCorpus.E68.Challenge",
                "solution_module": "Solutions.PalomarCorpus.E68",
                "theorem_names": ["PalomarCorpus.E68.Family.result"],
            }))
            (entry / "Challenge.lean").write_text("import Solutions.PalomarCorpus.E68\n")
            with self.assertRaisesRegex(ValueError, "only Mathlib"):
                axioms.run_palomar_audits(["PalomarCorpus/E68"])

    def test_git_pointer_file_is_metadata_but_source_leaks_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '.git').write_text('gitdir: /' + 'Users/example/private/worktrees/cut\n')
            (root / 'source.txt').write_text('Local root: /' + 'Users/example/private\n')
            findings = snapshot._private_text_findings(root)
            self.assertEqual(findings, [{'path': 'source.txt', 'kind': 'absolute_user_path'}])
            self.assertEqual([row['path'] for row in snapshot._tree_file_rows(root)], ['source.txt'])

    def test_git_directory_is_metadata_too(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '.git').mkdir()
            (root / '.git/config').write_text('worktree = /' + 'Users/example/private\n')
            self.assertEqual(snapshot._private_text_findings(root), [])
            self.assertEqual(snapshot._tree_file_rows(root), [])

    def fixture(self, root, entries):
        (root/'release-entries.json').write_text(json.dumps({'schema':'plectis_release_selection_v1', 'entries':entries, 'support_targets':[]}))
        (root/'lakefile.toml').write_text('defaultTargets = ["Solutions"]\n' + ''.join('[[lean_lib]]\nname = "'+e+'"\n' for e in set(entries)))
        for entry in set(entries):
            directory = root/entry; directory.mkdir(exist_ok=True)
            (directory/'comparator.json').write_text(json.dumps({'theorem_names':['example']}))
            for name in ['Challenge.lean','AxiomAudit.lean','formalization.yaml']:
                (directory/name).write_text('-- fixture\n')
            (root/'Solutions').mkdir(exist_ok=True)
            (root/'Solutions'/f'{entry}.lean').write_text('-- fixture\n')

    def test_focus_does_not_change_membership_or_build_obligations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); entries=['ExternalVerification257Example','ExternalVerification68Example']
            self.fixture(root, entries)
            auxiliary=root/'ExternalVerification1049Auxiliary';auxiliary.mkdir()
            (auxiliary/'comparator.json').write_text('{}')
            (auxiliary/'Challenge.lean').write_text('-- not selected')
            library_text=(root/'lakefile.toml').read_text().split('\n',1)[1]
            expected=None
            for focus in [['ErdosProblems.Erdos251.PaperLargeCertificateR7'],entries[:1],entries+['Solutions']]:
                (root/'lakefile.toml').write_text('defaultTargets = '+json.dumps(focus)+'\n'+library_text)
                with patch.object(release,'REPO_ROOT',root), patch.object(axioms,'REPO_ROOT',root):
                    result=release.build('test','test-commit')
                    identities=[row['entry'] for row in result['entries']]
                    self.assertEqual(axioms.entries(),identities)
                observed=(identities,result['required_build_targets'])
                if expected is None: expected=observed
                self.assertEqual(observed,expected)
                self.assertEqual(identities,sorted(entries))
                self.assertFalse(result['release_qualified'])

    def test_selected_incomplete_entry_still_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);entry='ExternalVerification257Example';self.fixture(root,[entry])
            for rel in [entry+'/comparator.json',entry+'/Challenge.lean',entry+'/AxiomAudit.lean',entry+'/formalization.yaml','Solutions/'+entry+'.lean']:
                path=root/rel;original=path.read_bytes();path.unlink()
                with self.subTest(path=rel),patch.object(release,'REPO_ROOT',root),self.assertRaisesRegex(ValueError,'Incomplete selected'):
                    release.build(None,'test-commit')
                path.write_bytes(original)

    def test_missing_empty_duplicate_and_source_only_do_not_waive_release(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);entry='ExternalVerification257Example';self.fixture(root,[entry])
            declaration=root/'release-entries.json'; valid=json.loads(declaration.read_text())
            for value, message in [(None,'Missing'),({**valid,'entries':[]},'Empty'),({**valid,'entries':[entry,entry]},'Duplicate'),({'schema':'source_only'},'source-only')]:
                if value is None: declaration.unlink()
                else: declaration.write_text(json.dumps(value))
                with self.subTest(value=value),patch.object(release,'REPO_ROOT',root),self.assertRaisesRegex(ValueError,message):
                    release.build(None,'test-commit')

    def test_release_plan_cannot_be_narrowed_by_focus(self):
        import build_launch_targets as runner
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);names=['ExternalVerification68A','ExternalVerification257B'];self.fixture(root,names)
            with patch.object(runner,'source_identity',return_value={}),patch.object(runner,'focused_targets',return_value=[]):
                plan=runner.make_plan(root,None,['ErdosProblems.Erdos251.PaperLargeCertificateR7'],False,True)
                self.assertEqual(plan['release_targets'],names)
                self.assertTrue(set(names)<=set(row['target'] for row in plan['targets']))
                with self.assertRaisesRegex(ValueError,'cannot qualify'):
                    runner.make_plan(root,None,['Focus'],True,True)

    def test_deployed_workflow_covers_independent_obligations(self):
        import release_inventory
        root=Path(__file__).resolve().parents[1]
        self.assertIn(release_inventory.validate_workflow_contract(root),
                      ['shared_release_inventory','legacy_complete_defaults'])

    def test_legacy_driver_cannot_hide_omitted_build_obligations(self):
        import release_inventory
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);names=['ExternalVerification68A','ExternalVerification257B'];self.fixture(root,names)
            workflow=root/'.github/workflows/release-gate.yml';workflow.parent.mkdir(parents=True)
            workflow.write_text('defaultTargets\nsubprocess.run(["lake", "build", target], check=True)')
            libraries=(root/'lakefile.toml').read_text().split('\n',1)[1]
            for focus in [['Research.Only'],names[:1]]:
                (root/'lakefile.toml').write_text('defaultTargets = '+json.dumps(focus)+'\n'+libraries)
                with self.assertRaisesRegex(ValueError,'would omit required builds'):
                    release_inventory.validate_workflow_contract(root)
            (root/'lakefile.toml').write_text('defaultTargets = '+json.dumps(names)+'\n'+libraries)
            self.assertEqual(release_inventory.validate_workflow_contract(root),'legacy_complete_defaults')

    def test_cli_retains_actionable_diagnostics_without_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);self.fixture(root,['ExternalVerification257Example'])
            (root/'release-entries.json').unlink()
            workflow=root/'.github/workflows/release-gate.yml';workflow.parent.mkdir(parents=True)
            workflow.write_text('defaultTargets\nsubprocess.run(["lake", "build", target], check=True)')
            output=root/'out/manifest.json';diagnostic=root/'out/diagnostics.json';summary=root/'summary.md'
            with patch.object(release,'REPO_ROOT',root),patch.object(sys,'argv',['build_release_manifest.py','--commit','exact-candidate','--out',str(output),'--diagnostics',str(diagnostic)]),patch.dict(os.environ,{'GITHUB_STEP_SUMMARY':str(summary)}):
                self.assertEqual(release.main(),1)
            report=json.loads(diagnostic.read_text())
            self.assertEqual(report['status'],'fail')
            self.assertEqual(report['commit'],'exact-candidate')
            self.assertIn('Missing',report['error'])
            self.assertIn('repair_route',report)
            self.assertFalse(output.exists())
            self.assertIn('exact-candidate',summary.read_text())


if __name__ == '__main__':
    unittest.main()
