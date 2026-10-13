"""Source batch diagnostics retain failures without authoring proof identity."""
import contextlib
import ast
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import build_launch_targets as runner
import fc_current_source_batch as batch


def check_native_library_registry(targets, library_roots, declared_libraries):
    """Exercise the registry lookup required before native library attachment."""
    if set(targets) != set(library_roots):
        raise ValueError('native target/library registry keys differ')
    for unit, row in targets.items():
        actual = declared_libraries[row[3]]
        if not actual <= library_roots[unit] or row[4].split('.')[0] not in actual:
            raise ValueError('unreviewed or missing native library for ' + unit)


class NativeLibraryRegistryTests(unittest.TestCase):
    def registry(self):
        root = Path(__file__).resolve().parent.parent
        tree = ast.parse((root / 'scripts/fc_receiving_identity.py').read_text())
        values = {node.targets[0].id: ast.literal_eval(node.value) for node in tree.body
                  if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name)
                  and node.targets[0].id in {'TARGETS', 'LIBRARY_ROOTS'}}
        targets, libraries = values['TARGETS'], values['LIBRARY_ROOTS']
        # Git blobs provide the immutable Lake files even in a sparse worktree.
        # Candidate Python is parsed as data and never executed by this test.
        declared = {}
        for project in {row[3] for row in targets.values()}:
            lake = subprocess.check_output(['git', '-C', str(root), 'show',
                'HEAD:verification/' + project + '/lakefile.toml'], text=True)
            declared[project] = {lib['name'] for lib in tomllib.loads(lake)['lean_lib']}
        return targets, libraries, declared

    def test_native_registry_covers_actual_lake_libraries(self):
        targets, libraries, declared = self.registry()
        check_native_library_registry(targets, libraries, declared)
        self.assertEqual(libraries['1049-order-coeff'],
                         declared[targets['1049-order-coeff'][3]])
        self.assertEqual(libraries['1049-order-coeff'],
                         {'ErdosProblems', 'FC1049OrderCoeffSolution'})

    def test_native_registry_rejects_missing_target_library_selection(self):
        targets, libraries, declared = self.registry()
        libraries.pop('1049-order-coeff')
        with self.assertRaisesRegex(ValueError, 'registry keys differ'):
            check_native_library_registry(targets, libraries, declared)

    def test_native_registry_rejects_unreviewed_actual_library(self):
        targets, libraries, declared = self.registry()
        declared[targets['1049-order-coeff'][3]].add('UnreviewedCandidate')
        with self.assertRaisesRegex(ValueError, 'unreviewed or missing'):
            check_native_library_registry(targets, libraries, declared)


class SourceBatchTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.report = self.root / '.lake' / 'report.json'
        (self.root / 'scripts').mkdir()
        (self.root / '.gitignore').write_text('.lake/\n')
        groups = [('FC249RationalObservableCurrent', ['6579']), ('FCSharpCurrent', ['6576']),
                  ('FCCountableCurrent', ['6577']), ('FCContourCurrent', ['6527']),
                  ('FCDualCurrent', ['6523-cubic', '6523-product']),
                  ('FCWeightedCurrent', ['6528-finite', '6528-mixed']),
                  ('FCReciprocalCurrent', ['6529']), ('FCHankelCurrent', ['6780']),
                  ('FCIntegerCurrent', ['6971-257', '6971-1049', '6971-258']),
                  ('FCHausdorffCurrent', ['6971-1041'])]
        manifest = json.dumps({'packages': [{'name': 'mathlib', 'rev': batch.MATHLIB}]})
        self.addCleanup(patch.stopall)
        patch.object(batch, 'MANIFEST', hashlib.sha256(manifest.encode()).hexdigest()).start()
        patch.dict(os.environ, {'GITHUB_STEP_SUMMARY': str(self.root / '.lake/summary.md')}).start()
        registry = {}
        for index, (name, units) in enumerate(groups):
            package = self.root / 'verification' / name
            package.mkdir(parents=True)
            module = f'FCResult{index}'
            source = 'theorem result : True := by trivial\n'
            (package / (module + '.lean')).write_text(source)
            (package / 'lean-toolchain').write_text(batch.TOOLCHAIN + '\n')
            (package / 'lake-manifest.json').write_text(manifest)
            (package / 'lakefile.toml').write_text(f'name = "fixture{index}"\ndefaultTargets = ["{module}"]\n')
            source_hash = 'sha256:' + hashlib.sha256(source.encode()).hexdigest()
            (package / 'source-binding.json').write_text(json.dumps({
                'receiving_pins': {'lean': batch.TOOLCHAIN, 'mathlib': batch.MATHLIB},
                'source_files': {module + '.lean': source_hash}, 'wrapper_sha256': source_hash}))
            for unit in units:
                registry[unit] = ('a' * 40, 'FormalConjectures/Fixture.lean', 'Fixture', name, module, 'Fixture.result')
        # Reading the native registry must not execute the candidate helper.
        (self.root / 'scripts/fc_receiving_identity.py').write_text('TARGETS = ' + repr(registry) + '\nraise RuntimeError("do not execute")\n')
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        runner.git('config', 'user.email', 'fixture@example.com', root=self.root)
        runner.git('config', 'user.name', 'Fixture', root=self.root)
        runner.git('config', 'commit.gpgSign', 'false', root=self.root)
        runner.git('config', 'core.hooksPath', '/dev/null', root=self.root)
        self.commit = self.commit_files()

    def commit_files(self):
        runner.git('add', '.', root=self.root)
        runner.git('commit', '-qm', 'fixture snapshot', root=self.root)
        return runner.git('rev-parse', 'HEAD', root=self.root)

    def plan(self):
        return batch.plan_batch(self.root, self.commit)

    def test_plan_covers_exact_units_and_independent_projects(self):
        plan = self.plan()
        self.assertEqual({u for p in plan['projects'] for u in p['units']}, batch.UNITS)
        self.assertEqual(len(plan['projects']), 10)
        self.assertEqual(len({p['path'] for p in plan['projects']}), 10)
        self.assertTrue(all(p['plan']['source']['commit'] == self.commit for p in plan['projects']))
        self.assertIn('No actual FC export', plan['boundary'])

    def test_plan_refuses_manifest_wrapper_and_population_drift(self):
        first = self.root / batch.SETUP_PROJECT
        for filename, text in [('lake-manifest.json', '{}'),
                               ('FCResult0.lean', 'theorem changed : False := by sorry\n'),
                               ('lakefile.toml', 'defaultTargets = ["Other"]\n')]:
            with self.subTest(filename=filename):
                saved = (first / filename).read_bytes()
                (first / filename).write_text(text)
                self.commit = self.commit_files()
                with self.assertRaises(ValueError):
                    self.plan()
                (first / filename).write_bytes(saved)
                self.commit = self.commit_files()
        registry = self.root / 'scripts/fc_receiving_identity.py'
        registry.write_text("TARGETS = {'6579': ()}\n")
        self.commit = self.commit_files()
        with self.assertRaisesRegex(ValueError, 'fourteen'):
            self.plan()

    def test_plan_refuses_wrong_commit_and_dirty_source(self):
        with self.assertRaisesRegex(ValueError, 'immutable'):
            batch.plan_batch(self.root, 'b' * 40)
        (self.root / batch.SETUP_PROJECT / 'FCResult0.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'clean'):
            self.plan()

    def test_exact_selection_builds_only_selected_projects(self):
        plan = batch.plan_batch(self.root, self.commit, ['6579'])
        self.assertEqual(plan['selected_units'], ['6579'])
        self.assertEqual(set(plan['omitted_units']), batch.UNITS - {'6579'})
        self.assertEqual([p['path'] for p in plan['projects']], [batch.SETUP_PROJECT])
        calls = []
        def build(*args, **kwargs):
            calls.append(args[0])
            runner.save_report(args[1], {'status': 'pass', 'targets': []})
            return 0
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(batch.compile_batch(self.root, plan, self.report, build=build), 0)
        self.assertEqual(len(calls), 1)
        for units in ([], ['6579', '6579'], ['unknown'], ['68-liminf']):
            with self.subTest(units=units), self.assertRaisesRegex(ValueError, 'nonempty, unique'):
                batch.plan_batch(self.root, self.commit, units)

    def test_reviewed_addition_does_not_drop_existing_registry_or_share_builds(self):
        registry_path = self.root / 'scripts/fc_receiving_identity.py'
        registry = ast.literal_eval(ast.parse(registry_path.read_text()).body[0].value)
        import shutil
        name = 'FC68CommonDenominatorCurrent'
        shutil.copytree(self.root / batch.SETUP_PROJECT, self.root / 'verification' / name)
        registry['68-liminf'] = ('', 'FormalConjectures/Paper/FactorialCommonDenominator.lean',
                                'FormalConjectures.Paper.FactorialCommonDenominator', name,
                                'FCResult0', 'FactorialCommonDenominator.growth_liminf')
        registry_path.write_text('TARGETS = ' + repr(registry) + '\n')
        self.commit = self.commit_files()
        plan = batch.plan_batch(self.root, self.commit, ['68-liminf'])
        self.assertEqual(len(plan['projects']), 1)
        self.assertEqual(plan['projects'][0]['path'], 'verification/' + name)
        self.assertEqual(set(plan['omitted_units']), batch.UNITS)
        self.assertEqual(len(self.plan()['projects']), 11)
        registry.pop('6579')
        registry_path.write_text('TARGETS = ' + repr(registry) + '\n')
        self.commit = self.commit_files()
        with self.assertRaisesRegex(ValueError, 'fourteen'):
            batch.plan_batch(self.root, self.commit, ['68-liminf'])

    def replay(self, failure=0, damage=False):
        plan = self.plan()
        calls = []
        def compile(argv, *, root, log, **kwargs):
            calls.append((argv, root, log))
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_bytes(b'warning: fixture retained compiler output')
            if damage and len(calls) == 10:
                (self.root / batch.SETUP_PROJECT / 'FCResult0.lean').write_text('changed by later source')
            return {'returncode': failure if len(calls) == 1 else 0, 'errors': [], 'seconds': 0.01}
        with patch.object(runner, 'run_build', compile), contextlib.redirect_stdout(io.StringIO()):
            code = batch.compile_batch(self.root, plan, self.report)
        return code, calls, json.loads(self.report.read_text())

    def test_failed_project_retains_all_later_reports_and_logs(self):
        code, calls, report = self.replay(failure=1)
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'fail')
        self.assertEqual(len(calls), 10)
        self.assertTrue(all(argv[:2] == ['lake', 'build'] and '--wfail' not in argv for argv, _, _ in calls))
        self.assertEqual(len({root for _, root, _ in calls}), 10)
        self.assertEqual(len({log for _, _, log in calls}), 10)
        self.assertTrue(all(log.exists() for _, _, log in calls))
        self.assertTrue(all(b'warning:' in log.read_bytes() for _, _, log in calls))
        self.assertFalse(report['warning_clean_required'])
        self.assertTrue(all(p['warning_clean_required'] is False for p in report['projects']))
        self.assertEqual([p['status'] for p in report['projects']], ['fail'] + ['pass'] * 9)
        self.assertTrue(all(Path(p['report']).exists() for p in report['projects']))
        self.assertEqual(report['kind'], 'fc_current_source_diagnostics')
        self.assertNotIn('verified', report)

    def test_later_source_mutation_cannot_leave_earlier_project_pass_authoritative(self):
        code, calls, report = self.replay(damage=True)
        self.assertEqual(len(calls), 10)
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'incomplete')
        self.assertTrue(report['source_changed'])

    def test_success_stays_source_only(self):
        code, _, report = self.replay()
        self.assertEqual(code, 0)
        self.assertEqual(report['status'], 'pass')
        self.assertFalse(report['warning_clean_required'])
        self.assertNotIn('warning_clean', report)
        self.assertIn('no receiving identity certification', report['boundary'])

    def test_dependency_sharing_does_not_share_candidate_outputs(self):
        plan = self.plan()
        shared = self.root / batch.SETUP_PROJECT / '.lake/packages'
        (shared / 'mathlib').mkdir(parents=True)
        with patch.object(runner, 'git', lambda *args, **kwargs: batch.MATHLIB if args[0] == 'rev-parse' else ''):
            batch.share_dependencies(self.root, plan)
            batch.share_dependencies(self.root, plan)
        for project in plan['projects']:
            lake = self.root / project['path'] / '.lake'
            self.assertEqual((lake / 'packages').resolve(), shared.resolve())
            self.assertFalse((lake / 'build').is_symlink())
        other = self.root / plan['projects'][1]['path'] / '.lake'
        (other / 'build').symlink_to(self.root / batch.SETUP_PROJECT / '.lake/build')
        with patch.object(runner, 'git', lambda *args, **kwargs: batch.MATHLIB if args[0] == 'rev-parse' else ''):
            with self.assertRaisesRegex(ValueError, 'project-local'):
                batch.share_dependencies(self.root, plan)

    def test_unpinned_or_dirty_hydrated_dependency_is_rejected(self):
        plan = self.plan()
        shared = self.root / batch.SETUP_PROJECT / '.lake/packages'
        (shared / 'mathlib').mkdir(parents=True)
        for actual, status in [('b' * 40, ''), (batch.MATHLIB, ' M Source.lean')]:
            with self.subTest(actual=actual, status=status):
                with patch.object(runner, 'git', lambda *args, **kwargs: actual if args[0] == 'rev-parse' else status):
                    with self.assertRaisesRegex(ValueError, 'hydrated'):
                        batch.share_dependencies(self.root, plan)


class WarningPolicyTests(unittest.TestCase):
    def test_explicit_warning_clean_flag_preserves_default_command(self):
        with tempfile.TemporaryDirectory() as directory:
            for explicit, expected in [(False, ['lake', 'build', 'Fixture']),
                                       (True, ['lake', '--wfail', 'build', 'Fixture'])]:
                calls = []
                def run(argv, check):
                    calls.append(argv)
                    return subprocess.CompletedProcess(argv, 0)
                with contextlib.redirect_stdout(io.StringIO()):
                    code = runner.build_targets(['Fixture'], Path(directory) / 'report.json', run,
                                                warning_clean=explicit)
                self.assertEqual(code, 0)
                self.assertEqual(calls, [expected])

    def test_cli_forwards_only_the_explicit_warning_policy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / 'lakefile.toml'
            config.write_text('defaultTargets = ["Fixture"]\n')
            for flag in (False, True):
                argv = ['build_launch_targets.py', '--repository', str(root), '--lakefile', str(config),
                        '--report', str(root / 'report.json'), *(['--wfail'] if flag else [])]
                with patch('sys.argv', argv), patch.object(runner, 'build_targets', return_value=0) as build:
                    self.assertEqual(runner.main(), 0)
                self.assertEqual(build.call_args.kwargs['warning_clean'], flag)


if __name__ == '__main__':
    unittest.main()
