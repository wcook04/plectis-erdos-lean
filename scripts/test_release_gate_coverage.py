# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed checks for source-bound Release Gate coverage."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

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
        payload = b'{"errors": []}'
        (audit_dir / 'palomar-axiom-audit.json').write_bytes(payload)
        (audit_dir / 'audit-receipt.json').write_text(json.dumps({
            'schema': gate.AUDIT_SCHEMA,
            'status': 'pass',
            'source': self.source,
            'plan_sha256': self.plan['plan_sha256'],
            'payload_sha256': hashlib.sha256(payload).hexdigest(),
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


if __name__ == '__main__':
    unittest.main()
