#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Compile current FC proof projects for diagnostics, never receiving identity.

Read the source snapshot's existing native target registry without executing it.
The ten projects share only their identical pinned dependencies; candidate source
roots and build outputs stay separate. Each project uses the convenience runner.
Warnings remain in compiler logs; ordinary Lake builds match the existing
candidate compilation policy without stopping later diagnostics on warnings.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

import build_launch_targets as runner

TOOLCHAIN = 'leanprover/lean4:v4.33.1'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
MANIFEST = 'c8ffc0d59f492007162fe54c68396e4b9f2f305fcf69210a7fbaf0b18fcd8cd9'
SETUP_PROJECT = 'verification/FC249RationalObservableCurrent'
UNITS = {'6579', '6576', '6577', '6527', '6523-cubic', '6523-product',
         '6528-finite', '6528-mixed', '6529', '6780', '6971-257',
         '6971-1049', '6971-258', '6971-1041'}
BOUNDARY = ('Source compiler diagnostics only. No actual FC export, Comparator, '
            'defaultLean or NanoDa acceptance; no receiving identity certification.')


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plan_batch(root: Path, commit: str) -> dict:
    if not re.fullmatch('[0-9a-f]{40}', commit) or runner.git('rev-parse', 'HEAD', root=root) != commit:
        raise ValueError('batch source must equal the selected immutable commit')
    if runner.git('status', '--porcelain', root=root):
        raise ValueError('batch source checkout must be clean')
    registry = root / 'scripts/fc_receiving_identity.py'
    assignments = [n.value for n in ast.parse(registry.read_text()).body
                   if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'TARGETS'
                                                       for t in n.targets)]
    if len(assignments) != 1:
        raise ValueError('native target registry is ambiguous')
    targets = ast.literal_eval(assignments[0])
    if not isinstance(targets, dict) or set(targets) != UNITS:
        raise ValueError('batch must cover all fourteen existing native units')
    projects = {}
    for unit, row in targets.items():
        if (not isinstance(row, tuple) or len(row) != 6 or not all(isinstance(v, str) for v in row)
                or not re.fullmatch(r'FC\w+Current', row[3]) or not runner.MODULE.fullmatch(row[4])):
            raise ValueError('invalid existing native project selection')
        project = projects.setdefault(row[3], {'path': 'verification/' + row[3], 'units': [], 'modules': []})
        project['units'].append(unit)
        if row[4] not in project['modules']:
            project['modules'].append(row[4])
    if len(projects) != 10:
        raise ValueError('batch must cover the ten distinct current FC projects')
    if projects[targets['6579'][3]]['path'] != SETUP_PROJECT:
        raise ValueError('primary native unit differs from the workflow dependency setup project')
    dependencies = None
    for project in projects.values():
        package = root / project['path']
        if package.is_symlink() or package.resolve().parent != (root / 'verification').resolve():
            raise ValueError('project escapes the selected source checkout')
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'source-binding.json'):
            if (package / name).is_symlink():
                raise ValueError('project metadata may not be symlinked')
        if (package / 'lean-toolchain').read_text().strip() != TOOLCHAIN or digest(package / 'lake-manifest.json') != MANIFEST:
            raise ValueError('project differs from the fixed receiving compiler/dependency manifest')
        manifest = json.loads((package / 'lake-manifest.json').read_text())
        current = {p['name']: p['rev'] for p in manifest['packages']}
        if (current.get('mathlib') != MATHLIB or len(current) != len(manifest['packages'])
                or any(not re.fullmatch('[0-9a-f]{40}', v) for v in current.values())):
            raise ValueError('dependency selection is incomplete or unpinned')
        if dependencies is not None and current != dependencies:
            raise ValueError('projects cannot share different dependencies')
        dependencies = current
        config = tomllib.loads((package / 'lakefile.toml').read_text())
        if config.get('defaultTargets') != project['modules']:
            raise ValueError('project defaults do not cover its selected solution modules')
        binding_path = package / 'source-binding.json'
        binding = json.loads(binding_path.read_text())
        pins = binding.get('receiving_pins', {'lean': binding.get('toolchain'), 'mathlib': binding.get('mathlib_commit')})
        if pins != {'lean': TOOLCHAIN, 'mathlib': MATHLIB}:
            raise ValueError('source binding receiving environment differs')
        files = binding.get('source_files', binding.get('original_source_files'))
        if isinstance(files, dict):
            hashes = files.items()
        elif isinstance(files, list) and files:
            hashes = [(f['port_path'], f['port_sha256']) for f in files]
        else:
            raise ValueError('source binding lacks port file digests')
        for name, expected in hashes:
            path = package / name
            if path.is_symlink() or not path.resolve().is_relative_to(package.resolve()) or 'sha256:' + digest(path) != expected:
                raise ValueError('source binding port bytes differ: ' + name)
        wrapper = binding.get('wrapper_sha256', binding.get('solution_sha256'))
        if wrapper and (len(project['modules']) != 1 or 'sha256:' + digest(package / (project['modules'][0] + '.lean')) != wrapper):
            raise ValueError('source binding solution wrapper bytes differ')
        project['source_binding_sha256'] = digest(binding_path)
        project['plan'] = runner.make_plan(package, None, [], False)
    return {'source_commit': commit, 'registry_sha256': digest(registry), 'dependencies': dependencies,
            'toolchain': TOOLCHAIN, 'manifest_sha256': MANIFEST, 'projects': list(projects.values()),
            'setup_project': SETUP_PROJECT, 'driver_sha256': digest(Path(__file__)),
            'warning_clean_required': False, 'boundary': BOUNDARY}


def share_dependencies(root: Path, plan: dict) -> None:
    shared = root / plan['setup_project'] / '.lake/packages'
    if shared.is_symlink() or not shared.is_dir():
        raise ValueError('first project must hydrate its pinned dependencies before batch compilation')
    for name, commit in plan['dependencies'].items():
        dependency = shared / name
        if (dependency.is_symlink() or runner.git('rev-parse', 'HEAD', root=dependency) != commit
                or runner.git('status', '--porcelain', '--untracked-files=no', root=dependency)):
            raise ValueError('hydrated dependency source differs: ' + name)
    for project in plan['projects']:
        lake = root / project['path'] / '.lake'
        if lake.is_symlink() or (lake / 'build').is_symlink():
            raise ValueError('candidate build outputs must remain project-local')
        lake.mkdir(exist_ok=True)
        destination = lake / 'packages'
        if destination == shared:
            continue
        if destination.is_symlink():
            if destination.resolve() != shared.resolve():
                raise ValueError('project points to another dependency cache')
        elif destination.exists():
            raise ValueError('project already has an independent dependency directory')
        else:
            destination.symlink_to(shared.resolve(), target_is_directory=True)


def compile_batch(root: Path, plan: dict, report: Path, *, build=runner.build_targets,
                  project_budget: float = 1500) -> int:
    result = {'schema_version': 2, 'kind': 'fc_current_source_diagnostics', 'status': 'running',
              'plan': plan, 'warning_clean_required': False, 'boundary': BOUNDARY, 'projects': []}
    runner.save_report(report, result)
    for project in plan['projects']:
        package = root / project['path']
        project_report = report.parent / 'fc-current-source-batch' / package.name / 'report.json'
        row = {'path': project['path'], 'units': project['units'], 'report': str(project_report),
               'warning_clean_required': False, 'status': 'incomplete'}
        try:
            code = build(project['modules'], project_report, plan=project['plan'], root=package,
                         keep_going=True, warning_clean=False, total_budget=project_budget)
            detail = json.loads(project_report.read_text())
            row.update(status=detail['status'], returncode=code, targets=detail['targets'])
        except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
            row['error'] = str(error)
        result['projects'].append(row)
        runner.save_report(report, result)
    if (runner.git('rev-parse', 'HEAD', root=root) != plan['source_commit']
            or runner.git('status', '--porcelain', root=root)):
        result['source_changed'] = True
    for project in plan['projects']:
        package = root / project['path']
        if (runner.source_identity(package) != project['plan']['source']
                or digest(package / 'source-binding.json') != project['source_binding_sha256']):
            result['source_changed'] = True
    result['status'] = ('incomplete' if result.get('source_changed') or any(p['status'] not in ('pass', 'fail') for p in result['projects'])
                        else 'fail' if any(p['status'] == 'fail' for p in result['projects']) else 'pass')
    runner.save_report(report, result)
    print(json.dumps({'status': result['status'], 'projects': result['projects'], 'boundary': BOUNDARY}, indent=2))
    return 0 if result['status'] == 'pass' else 1


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--project-budget', type=runner.positive, default=1500,
                        help='seconds per project; default ten-project budget fits the shared CI job')
    args = parser.parse_args(argv)
    root, report = args.repository.resolve(), args.report.resolve()
    try:
        plan = plan_batch(root, args.source_commit)
        if args.plan:
            runner.save_report(report, {'schema_version': 2, 'kind': 'fc_current_source_diagnostics',
                                        'status': 'planned', 'plan': plan,
                                        'warning_clean_required': False, 'boundary': BOUNDARY})
            return 0
        share_dependencies(root, plan)
        return compile_batch(root, plan, report, project_budget=args.project_budget)
    except (OSError, ValueError, KeyError, TypeError, SyntaxError, subprocess.SubprocessError) as error:
        runner.save_report(report, {'schema_version': 2, 'kind': 'fc_current_source_diagnostics',
                                    'status': 'incomplete', 'error': str(error),
                                    'warning_clean_required': False, 'boundary': BOUNDARY})
        print('::error::' + runner.annotation(str(error)))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
