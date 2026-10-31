# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Source-root, release-path and repository-layout compatibility checks."""
import json
import os
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import patch

from corpus_paths import corpus_path, source_root, relative_path
import build_release_manifest as release
import palomar_entry_names


class CorpusPaths(unittest.TestCase):
    def test_package_and_library_source_roots_keep_module_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'lakefile.toml').write_text('srcDir = "source"\n[[lean_lib]]\nname = "ExternalVerification68One"\nsrcDir = "families"\n[[lean_lib]]\nname = "Solutions"\nsrcDir = "proofs"\n')
            self.assertEqual(corpus_path(root, 'ExternalVerification68One/Challenge.lean'), root/'source/families/ExternalVerification68One/Challenge.lean')
            self.assertEqual(corpus_path(root, 'ExternalVerification68New/Challenge.lean'), root/'source/families/ExternalVerification68New/Challenge.lean')
            self.assertEqual(relative_path(root, 'Solutions/One.lean'), 'source/proofs/Solutions/One.lean')
            self.assertEqual(corpus_path(root, 'source/proofs/Solutions/One.lean'), root/'source/proofs/Solutions/One.lean')

    def test_ambiguous_family_roots_and_escape_are_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'lakefile.toml').write_text('[[lean_lib]]\nname="ExternalVerification68One"\nsrcDir="one"\n[[lean_lib]]\nname="ExternalVerification68Two"\nsrcDir="two"\n')
            with self.assertRaisesRegex(ValueError, 'ambiguous'):
                source_root(root, 'ExternalVerification68New')
            (root/'lakefile.toml').write_text('[[lean_lib]]\nname="Solutions"\nsrcDir="../outside"\n')
            with self.assertRaisesRegex(ValueError, 'escapes'):
                source_root(root, 'Solutions')
            with self.assertRaises(ValueError):
                corpus_path(root, '../outside')

    def test_release_manifest_emits_filesystem_paths_and_preserves_entry_ids(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = 'ExternalVerification68Example'
            (root/'lakefile.toml').write_text(f'[[lean_lib]]\nname="{entry}"\nsrcDir="proofs/families"\n[[lean_lib]]\nname="Solutions"\nsrcDir="proofs"\n')
            family = corpus_path(root, entry);family.mkdir(parents=True)
            (family/'comparator.json').write_text(json.dumps({'challenge_module':entry+'.Challenge','solution_module':'Solutions.'+entry,'theorem_names':['exact.statement'],'permitted_axioms':[]}))
            for name in ['Challenge.lean','AxiomAudit.lean','formalization.yaml']:
                (family/name).write_text('-- fixture\n')
            proof=corpus_path(root, 'Solutions/'+entry+'.lean');proof.parent.mkdir(parents=True);proof.write_text('-- complete fixture\n')
            with patch.object(release, 'REPO_ROOT', root):
                row = release.entry_row(entry)
            self.assertEqual(row['entry'], entry)
            self.assertEqual(row['challenge_module'], entry+'.Challenge')
            self.assertEqual(row['comparator_config_path'], f'proofs/families/{entry}/comparator.json')
            self.assertEqual(row['solution_path'], f'proofs/Solutions/{entry}.lean')
            for field in ['comparator_config_path','challenge_path','solution_path','axiom_audit_path','formalization_metadata_path']:
                self.assertTrue((root/row[field]).is_file(), field)

    def test_actual_corpus_libraries_and_publication_population_resolve(self):
        root=Path(__file__).resolve().parents[1]
        config=tomllib.loads((root/'lakefile.toml').read_text())
        libraries={row['name']:row for row in config['lean_lib']}
        families={name for name in libraries if name.startswith('ExternalVerification')}
        physical={path.name for path in (root/'proofs/families').iterdir() if path.is_dir()}
        self.assertTrue(families <= physical)
        for name in physical:
            self.assertTrue((corpus_path(root,name)/'Challenge.lean').is_file())
            self.assertTrue(corpus_path(root,'Solutions/'+name+'.lean').is_file())
        self.assertFalse(any(root.glob('ExternalVerification*')))
        for name in families:
            self.assertEqual(libraries[name].get('srcDir'), 'proofs/families')
            self.assertTrue((corpus_path(root,name)/'comparator.json').is_file())
        for name in palomar_entry_names.discover(root):
            self.assertTrue(corpus_path(root,f'PalomarCorpus/{name}/Challenge.lean').is_file())
            self.assertTrue(corpus_path(root,f'Solutions/PalomarCorpus/{name}.lean').is_file())


class TrustedSourceLayout(unittest.TestCase):
    def test_trusted_caller_selects_historical_and_nested_sources_without_loading_scripts(self):
        root=Path(__file__).resolve().parents[1]
        workflow=(root/'.github/workflows/fc-trusted-comparator-preflight.yml').read_text()
        block=workflow.split('      - name: Check selected source without executing it',1)[1].split("          python3 - <<'PY'\n",1)[1].split('          PY',1)[0]
        code='\n'.join(line[10:] for line in block.splitlines())
        for prefix in ['PalomarCorpus','proofs/PalomarCorpus']:
            with self.subTest(prefix=prefix), tempfile.TemporaryDirectory() as directory:
                base=Path(directory);source=base/'source';source.mkdir()
                (source/'lean-toolchain').write_text('leanprover/lean4:v4.30.0\n')
                entry=source/prefix/'E68_01';entry.mkdir(parents=True)
                config={'challenge_module':'PalomarCorpus.E68_01.Challenge','solution_module':'Solutions.PalomarCorpus.E68_01','theorem_names':['exact.statement'],'permitted_axioms':[],'enable_nanoda':True}
                (entry/'comparator.json').write_text(json.dumps(config))
                for name in ['Challenge.lean','formalization.yaml']:(entry/name).write_text('fixture\n')
                (source/'scripts').mkdir();(source/'scripts/corpus_paths.py').write_text('raise RuntimeError("untrusted source code executed")\n')
                output=base/'output';prior=Path.cwd()
                with patch.dict(os.environ, {'SOURCE_COMMIT':'a'*40,'ENTRY':'E68_01','GITHUB_OUTPUT':str(output)}), patch('subprocess.check_output', return_value='a'*40):
                    try:
                        os.chdir(base);exec(compile(code,'trusted-caller','exec'),{})
                    finally:os.chdir(prior)
                options=json.loads(output.read_text().strip().removeprefix('options='))
                self.assertEqual(options['comparator_config_path'],prefix+'/E68_01/comparator.json')
                self.assertEqual(options['formalization_metadata_path'],prefix+'/E68_01/formalization.yaml')


if __name__ == '__main__':
    unittest.main()
