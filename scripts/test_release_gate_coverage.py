# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed checks for source-bound Release Gate coverage."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import subprocess
import sys

import release_gate_coverage as gate


class ReleaseGateCoverageTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.artifacts = Path(temporary.name)
        self.source = {'commit': 'a' * 40, 'lakefile_sha256': 'b' * 64,
                       'lean_toolchain_sha256': 'c' * 64, 'lake_manifest_sha256': 'd' * 64}
        self.targets = [f'ExternalVerification{i}' for i in range(13)] + [
            'Solutions', 'PalomarCorpus']
        self.plan = gate.make_plan(self.targets, self.source)

    def write_receipts(self):
        for shard in self.plan['shards']:
            path = self.artifacts / f"release-target-{shard['id']}" / 'report.json'
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps({
                'status': 'pass',
                'release_gate': {'source': self.source,
                                 'plan_sha256': self.plan['plan_sha256'],
                                 'shard_id': shard['id']},
                'targets': [{'target': target, 'status': 'pass', 'returncode': 0}
                            for target in shard['targets']],
            }))
        audit_dir = self.artifacts / 'release-axiom-audit'
        audit_dir.mkdir()
        entry = 'PalomarCorpus/E68_01'
        outcome = {'entry': entry, 'status': 'pass', 'returncode': 0}
        audit_source = {'commit': self.source['commit'], 'source_file_count': 1,
                        'deleted_in_worktree': [], 'source_files_sha256': 'e' * 64}
        binding = {'mode': 'fresh_lake_lean', 'source_before': audit_source,
                   'source_after': audit_source, 'source_stable': True}
        payload = json.dumps({'status': 'ok', 'planned_entries': [entry],
                              'entries': [{'entry': entry, 'status': 'ok', 'execution': outcome}],
                              'source_binding': binding}).encode()
        progress = json.dumps({'schema': 'palomar_axiom_audit_progress_v1',
                               'source_before': binding['source_before'],
                               'planned_entries': [entry], 'outcomes': [outcome]}).encode()
        (audit_dir / 'palomar-axiom-audit.json').write_bytes(payload)
        (audit_dir / 'audit-progress.json').write_bytes(progress)
        (audit_dir / 'audit-receipt.json').write_text(json.dumps({
            'schema': gate.AUDIT_SCHEMA,
            'status': 'pass',
            'source': self.source,
            'plan_sha256': self.plan['plan_sha256'],
            'payload_sha256': hashlib.sha256(payload).hexdigest(),
            'progress_sha256': hashlib.sha256(progress).hexdigest(),
        }))

    def test_plan_is_exact_and_umbrellas_are_isolated(self):
        assigned = [target for shard in self.plan['shards'] for target in shard['targets']]
        self.assertCountEqual(assigned, self.targets)
        self.assertEqual(len(assigned), len(set(assigned)))
        for name in gate.UMBRELLAS:
            self.assertIn({'id': name, 'targets': [name]}, self.plan['shards'])

    def test_complete_green_receipts_pass(self):
        self.write_receipts()
        self.assertEqual(gate.check_coverage(self.plan, self.artifacts), [])

    def test_missing_shard_fails(self):
        self.write_receipts()
        (self.artifacts / 'release-target-Solutions' / 'report.json').unlink()
        self.assertIn('missing or invalid report: Solutions',
                      gate.check_coverage(self.plan, self.artifacts))

    def test_stale_source_and_partial_target_fail(self):
        self.write_receipts()
        path = self.artifacts / 'release-target-targets-1' / 'report.json'
        report = json.loads(path.read_text())
        report['release_gate']['source']['commit'] = 'e' * 40
        report['targets'][0]['status'] = 'not-attempted'
        path.write_text(json.dumps(report))
        issues = gate.check_coverage(self.plan, self.artifacts)
        self.assertIn('stale or mismatched report: targets-1', issues)
        self.assertIn('incomplete or failing target: targets-1', issues)

    def test_missing_target_and_audit_fail(self):
        self.write_receipts()
        path = self.artifacts / 'release-target-targets-2' / 'report.json'
        report = json.loads(path.read_text())
        report['targets'].pop()
        path.write_text(json.dumps(report))
        (self.artifacts / 'release-axiom-audit' / 'audit-receipt.json').unlink()
        issues = gate.check_coverage(self.plan, self.artifacts)
        self.assertIn('target population mismatch: targets-2', issues)
        self.assertIn('missing or invalid publication axiom audit', issues)

    def test_censored_audit_payload_fails_even_with_a_matching_receipt_hash(self):
        self.write_receipts()
        audit_dir = self.artifacts / 'release-axiom-audit'
        path = audit_dir / 'palomar-axiom-audit.json'
        payload = json.loads(path.read_text())
        payload['entries'] = []
        raw = json.dumps(payload).encode()
        path.write_bytes(raw)
        receipt_path = audit_dir / 'audit-receipt.json'
        receipt = json.loads(receipt_path.read_text())
        receipt['payload_sha256'] = hashlib.sha256(raw).hexdigest()
        receipt_path.write_text(json.dumps(receipt))
        self.assertIn('stale, incomplete, or failing publication axiom audit',
                      gate.check_coverage(self.plan, self.artifacts))

    def test_failed_audit_keeps_diagnostics_in_artifact(self):
        out_dir = self.artifacts / 'audit'
        argv = ['release_gate_coverage.py', 'audit', '--plan', 'unused',
                '--out-dir', str(out_dir)]
        failed = subprocess.CompletedProcess([], 1, stderr='E68 proof failure\n')
        with patch.object(sys, 'argv', argv), patch.object(gate, 'load_plan', return_value=self.plan), \
                patch.object(gate.subprocess, 'run', return_value=failed):
            self.assertEqual(gate.main(), 1)
        receipt = json.loads((out_dir / 'audit-receipt.json').read_text())
        diagnostics = (out_dir / 'diagnostics.log').read_bytes()
        self.assertEqual(receipt['status'], 'fail')
        self.assertEqual(diagnostics, b'E68 proof failure\n')
        self.assertEqual(receipt['diagnostics_sha256'], hashlib.sha256(diagnostics).hexdigest())


if __name__ == '__main__':
    unittest.main()
