#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Resolve source refs and retain diagnostics across CI setup failures."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import quote

from build_launch_targets import annotation, save_report


def resolve_source(repository, ref, api=subprocess.run):
    if not re.fullmatch(r'[\w.-]+/[\w.-]+', repository):
        raise ValueError('invalid repository name')
    if not ref or len(ref) > 1024 or any(ord(c) < 32 for c in ref):
        raise ValueError('source ref must be a branch, tag or commit')
    # The commits API accepts abbreviated SHAs; checkout treats them as names.
    result = api(['gh', 'api', f'repos/{repository}/commits/{quote(ref, safe="")}',
                  '--jq', '.sha'], text=True, capture_output=True, timeout=45, check=False)
    sha = result.stdout.strip()
    if result.returncode or not re.fullmatch(r'[0-9a-f]{40}', sha):
        raise ValueError(f'cannot resolve source ref {ref!r} to a commit in {repository}')
    return sha


def finalize(setup, target_report, steps):
    result = dict(setup)
    if target_report.exists():
        try:
            result.update(json.loads(target_report.read_text()))
        except (ValueError, OSError):
            result.update(status='incomplete', reason='unreadable_build_report')
    failed = {name: row.get('outcome') for name, row in steps.items()
              if row.get('outcome') in ('failure', 'cancelled')}
    result['workflow_steps'] = {name: row.get('outcome') for name, row in steps.items()}
    if failed or result.get('status') in (None, 'running', 'planned'):
        if result.get('status') != 'fail':
            result['status'] = 'incomplete'
        result['incomplete_steps'] = failed
    if 'plan' not in result:
        result.setdefault('reason', 'setup_did_not_reach_build')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['resolve', 'finalize'])
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--target-report', type=Path)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    if args.command == 'resolve':
        try:
            sha = resolve_source(os.environ['GITHUB_REPOSITORY'], report['requested_source'])
            report.update(resolved_source=sha, phase='source_checkout')
            save_report(args.report, report)
            with open(os.environ['GITHUB_OUTPUT'], 'a') as output:
                output.write(f'source_sha={sha}\n')
            print('Resolved source to ' + sha)
            return 0
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            report.update(status='incomplete', phase='source_resolution', error=str(error))
            save_report(args.report, report)
            print('::error::' + annotation(str(error)))
            return 2
    report = finalize(report, args.target_report, json.loads(os.environ['CI_STEPS_JSON']))
    save_report(args.report, report)
    if report['status'] == 'incomplete':
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as output:
            output.write('## Lean Convenience setup or execution incomplete\n\n'
                         'See the retained JSON report for the source ref and failed step.\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
