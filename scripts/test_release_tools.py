#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for release enumeration and checkout metadata boundaries."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_release_manifest as release
import verify_snapshot as snapshot


class ReleaseToolsTests(unittest.TestCase):
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

    def test_release_targets_ignore_auxiliary_challenge_directories(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = 'ExternalVerification257Example'
            (root / 'lakefile.toml').write_text(f'defaultTargets = ["{entry}", "Solutions"]\n')
            (root / entry).mkdir()
            (root / entry / 'comparator.json').write_text(json.dumps({'theorem_names': ['example']}))
            (root / entry / 'Challenge.lean').write_text('-- fixture\n')
            (root / 'ExternalVerification1049Auxiliary').mkdir()
            (root / 'ExternalVerification1049Auxiliary/Challenge.lean').write_text('-- not released\n')
            with patch.object(release, 'REPO_ROOT', root):
                result = release.build('test', 'test-commit')
            self.assertEqual(result['entry_count'], 1)
            self.assertEqual(result['problems'], ['257'])
            self.assertEqual(result['entries'][0]['entry'], entry)
            self.assertIn('all 1 of them', result['axiom_audit_note'])

    def test_selected_incomplete_entry_still_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'lakefile.toml').write_text('defaultTargets = ["ExternalVerification257Missing"]\n')
            with patch.object(release, 'REPO_ROOT', root), self.assertRaises(FileNotFoundError):
                release.build(None, 'test-commit')

    def test_empty_or_duplicate_release_targets_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for targets in ('["Solutions"]', '["ExternalVerification257A", "ExternalVerification257A"]'):
                (root / 'lakefile.toml').write_text(f'defaultTargets = {targets}\n')
                with self.subTest(targets=targets), patch.object(release, 'REPO_ROOT', root), self.assertRaises(ValueError):
                    release.build(None, 'test-commit')


if __name__ == '__main__':
    unittest.main()
