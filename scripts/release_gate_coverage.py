#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Plan, run, and reconcile every Release Gate target at one source commit.

Shards schedule the existing launch-target runner. The plan and final check,
not a shard count or a green matrix cell, define the coverage obligation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from build_launch_targets import build_targets, read_targets, save_report


PLAN_SCHEMA = 'release_gate_coverage_plan_v1'
AUDIT_SCHEMA = 'release_gate_axiom_audit_v1'
UMBRELLAS = ('Solutions', 'PalomarCorpus')


def digest(data: object) -> str:
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_identity(root: Path) -> dict[str, str]:
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    return {
        'commit': commit,
        'lakefile_sha256': file_digest(root / 'lakefile.toml'),
        'lean_toolchain_sha256': file_digest(root / 'lean-toolchain'),
        'lake_manifest_sha256': file_digest(root / 'lake-manifest.json'),
    }


def make_plan(targets: list[str], source: dict[str, str], ordinary_shards: int = 4) -> dict:
    if not targets or len(targets) != len(set(targets)):
        raise ValueError('expected distinct, nonempty defaultTargets')
    if ordinary_shards < 1:
        raise ValueError('ordinary_shards must be positive')
    ordinary = [target for target in targets if target not in UMBRELLAS]
    groups = [ordinary[index::ordinary_shards] for index in range(ordinary_shards)]
    shards = [{'id': f'targets-{index + 1}', 'targets': group}
              for index, group in enumerate(groups) if group]
    shards.extend({'id': name, 'targets': [name]} for name in UMBRELLAS if name in targets)
    assigned = [target for shard in shards for target in shard['targets']]
    if len(assigned) != len(targets) or set(assigned) != set(targets):
        raise ValueError('shard plan omits or duplicates a launch target')
    plan = {'schema': PLAN_SCHEMA, 'source': source, 'expected_targets': targets,
            'shards': shards}
    plan['plan_sha256'] = digest(plan)
    return plan


def load_plan(path: Path, root: Path) -> dict:
    plan = json.loads(path.read_text(encoding='utf-8'))
    checksum = plan.get('plan_sha256')
    if plan.get('schema') != PLAN_SCHEMA or checksum != digest({k: v for k, v in plan.items() if k != 'plan_sha256'}):
        raise ValueError('invalid or changed Release Gate plan')
    if plan['source'] != source_identity(root):
        raise ValueError('plan source or environment differs from this checkout')
    if plan['expected_targets'] != read_targets(root / 'lakefile.toml'):
        raise ValueError('plan does not cover current defaultTargets')
    expected = set(plan['expected_targets'])
    assigned = [target for shard in plan['shards'] for target in shard['targets']]
    if len(assigned) != len(expected) or set(assigned) != expected:
        raise ValueError('plan shard population does not equal defaultTargets')
    return plan


def check_coverage(plan: dict, artifacts: Path) -> list[str]:
    issues: list[str] = []
    for shard in plan['shards']:
        path = artifacts / f"release-target-{shard['id']}" / 'report.json'
        try:
            report = json.loads(path.read_text(encoding='utf-8'))
        except (OSError, json.JSONDecodeError):
            issues.append(f"missing or invalid report: {shard['id']}")
            continue
        if report.get('release_gate') != {'source': plan['source'], 'plan_sha256': plan['plan_sha256'],
                                           'shard_id': shard['id']}:
            issues.append(f"stale or mismatched report: {shard['id']}")
        rows = report.get('targets')
        if not isinstance(rows, list) or [row.get('target') for row in rows] != shard['targets']:
            issues.append(f"target population mismatch: {shard['id']}")
            continue
        if report.get('status') != 'pass' or any(row.get('status') != 'pass' or row.get('returncode') != 0 for row in rows):
            issues.append(f"incomplete or failing target: {shard['id']}")
    audit_dir = artifacts / 'release-axiom-audit'
    try:
        audit = json.loads((audit_dir / 'audit-receipt.json').read_text(encoding='utf-8'))
        payload = (audit_dir / 'palomar-axiom-audit.json').read_bytes()
        json.loads(payload)
    except (OSError, json.JSONDecodeError):
        issues.append('missing or invalid publication axiom audit')
    else:
        if (audit.get('schema') != AUDIT_SCHEMA or audit.get('status') != 'pass'
                or audit.get('source') != plan['source']
                or audit.get('plan_sha256') != plan['plan_sha256']
                or audit.get('payload_sha256') != hashlib.sha256(payload).hexdigest()):
            issues.append('stale, incomplete, or failing publication axiom audit')
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    plan_cmd = commands.add_parser('plan')
    plan_cmd.add_argument('--out', type=Path, required=True)
    plan_cmd.add_argument('--github-output', type=Path)
    run_cmd = commands.add_parser('run-shard')
    run_cmd.add_argument('--plan', type=Path, required=True)
    run_cmd.add_argument('--shard-id', required=True)
    run_cmd.add_argument('--report', type=Path, required=True)
    audit_cmd = commands.add_parser('audit')
    audit_cmd.add_argument('--plan', type=Path, required=True)
    audit_cmd.add_argument('--out-dir', type=Path, required=True)
    check_cmd = commands.add_parser('check-run')
    check_cmd.add_argument('--plan', type=Path, required=True)
    check_cmd.add_argument('--artifacts', type=Path, required=True)
    args = parser.parse_args()
    root = Path.cwd()
    try:
        if args.command == 'plan':
            plan = make_plan(read_targets(root / 'lakefile.toml'), source_identity(root))
            save_report(args.out, plan)
            ids = [shard['id'] for shard in plan['shards']]
            if args.github_output:
                with args.github_output.open('a', encoding='utf-8') as output:
                    output.write('shards=' + json.dumps(ids, separators=(',', ':')) + '\n')
            print(f"Release Gate plan: {len(plan['expected_targets'])} targets in {len(ids)} shards at {plan['source']['commit']}")
            return 0
        plan = load_plan(args.plan, root)
        if args.command == 'run-shard':
            shard = next((item for item in plan['shards'] if item['id'] == args.shard_id), None)
            if shard is None:
                raise ValueError(f'unknown shard: {args.shard_id}')
            metadata = {'source': plan['source'], 'plan_sha256': plan['plan_sha256'],
                        'shard_id': shard['id']}
            return build_targets(shard['targets'], args.report, metadata=metadata)
        if args.command == 'audit':
            args.out_dir.mkdir(parents=True, exist_ok=True)
            receipt_path = args.out_dir / 'audit-receipt.json'
            payload_path = args.out_dir / 'palomar-axiom-audit.json'
            diagnostics_path = args.out_dir / 'diagnostics.log'
            receipt = {'schema': AUDIT_SCHEMA, 'status': 'running', 'source': plan['source'],
                       'plan_sha256': plan['plan_sha256'], 'payload_sha256': None}
            save_report(receipt_path, receipt)
            with payload_path.open('w', encoding='utf-8') as output:
                result = subprocess.run([sys.executable, 'scripts/check_axiom_budget.py',
                                         '--run-palomar', '--json'], stdout=output,
                                        stderr=subprocess.PIPE, text=True, check=False)
            diagnostics_path.write_text(result.stderr, encoding='utf-8')
            if result.stderr:
                print(result.stderr, file=sys.stderr, end='')
            try:
                json.loads(payload_path.read_text(encoding='utf-8'))
                valid_json = True
            except json.JSONDecodeError:
                valid_json = False
            receipt['status'] = 'pass' if result.returncode == 0 and valid_json else 'fail'
            receipt['returncode'] = result.returncode
            receipt['payload_sha256'] = file_digest(payload_path)
            receipt['diagnostics_sha256'] = file_digest(diagnostics_path)
            save_report(receipt_path, receipt)
            return 0 if receipt['status'] == 'pass' else 1
        issues = check_coverage(plan, args.artifacts)
        for issue in issues:
            print(f'::error::{issue}', file=sys.stderr)
        if issues:
            return 1
        print(f"Release Gate complete: {len(plan['expected_targets'])} targets and publication audit at {plan['source']['commit']}")
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError, KeyError) as error:
        print(f'Release Gate incomplete: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
