#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Sequential Convenience replay with a complete target-level failure report.

This does not replace Palomar preflight or change the selected launch targets.
Ordinary build failures do not hide later targets. Interrupted/incomplete runs
and configuration errors fail closed; a partial result is never a pass.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib
from collections.abc import Callable, Sequence


def read_targets(path: Path) -> list[str]:
    with path.open('rb') as source:
        targets = tomllib.load(source).get('defaultTargets')
    if not isinstance(targets, list) or not targets:
        raise ValueError('defaultTargets must be a nonempty array')
    if any(not isinstance(t, str) or not t.strip() or t.startswith('-') for t in targets):
        raise ValueError('defaultTargets must contain nonempty, non-option target names')
    if len(set(targets)) != len(targets):
        raise ValueError('defaultTargets contains duplicate targets')
    return targets


def save_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    temporary.replace(path)


def build_targets(targets: Sequence[str], report_path: Path,
                  run: Callable = subprocess.run,
                  metadata: dict | None = None) -> int:
    if not targets:
        raise ValueError('refusing an empty target replay')
    rows = [{'target': target, 'status': 'not-attempted', 'returncode': None}
            for target in targets]
    report = {'schema_version': 1, 'status': 'running', 'targets': rows}
    if metadata is not None:
        report['release_gate'] = metadata
    save_report(report_path, report)
    interrupted = False
    for row in rows:
        row['status'] = 'running'
        save_report(report_path, report)
        target = row['target']
        print(f'=== lake build {target} ===', flush=True)
        try:
            result = run(['lake', 'build', target], check=False)
        except (OSError, KeyboardInterrupt) as error:
            row['status'] = 'incomplete'
            row['error'] = type(error).__name__ + ': ' + str(error)
            interrupted = True
        else:
            row['returncode'] = result.returncode
            # A signal or shell-style interruption is not an ordinary proof
            # failure. Do not start more work after cancellation or an OOM kill.
            if result.returncode < 0 or result.returncode in (130, 137, 143):
                row['status'] = 'incomplete'
                interrupted = True
            else:
                row['status'] = 'pass' if result.returncode == 0 else 'fail'
        save_report(report_path, report)
        if interrupted:
            break
    report['status'] = ('incomplete' if interrupted else
                        'fail' if any(r['status'] != 'pass' for r in rows) else 'pass')
    save_report(report_path, report)
    lines = ['## Lean Convenience target replay', '',
             f"Overall: **{report['status']}**. These are launch targets, not module counts.",
             '', '| Target | Result | Exit code |', '| --- | --- | --- |']
    for row in rows:
        name = row['target'].replace('|', '\\|').replace('\n', ' ')
        code = '-' if row['returncode'] is None else str(row['returncode'])
        lines.append(f"| `{name}` | {row['status']} | {code} |")
    summary = '\n'.join(lines) + '\n'
    print(summary, flush=True)
    if destination := os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(destination, 'a', encoding='utf-8') as output:
            output.write(summary)
    return 2 if interrupted else (1 if report['status'] == 'fail' else 0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lakefile', type=Path, default=Path('lakefile.toml'))
    parser.add_argument('--report', type=Path,
                        default=Path('.lake/convenience-target-report.json'))
    args = parser.parse_args()
    # Remove an old report before parsing, so bad configuration cannot leave
    # a previous pass looking like evidence for this invocation.
    try:
        args.report.unlink(missing_ok=True)
        targets = read_targets(args.lakefile)
        return build_targets(targets, args.report)
    except (OSError, ValueError) as error:
        print(f'Convenience replay could not complete: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
