"""Source batch diagnostics retain failures without authoring proof identity."""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import build_launch_targets as runner
import fc_current_source_batch as batch


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

    def replay(self, failure=0, damage=False):
        plan = self.plan()
        calls = []
        def compile(argv, *, root, log, **kwargs):
            calls.append((argv, root, log))
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_bytes(b'fixture retained compiler output')
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
        self.assertTrue(all(argv[:3] == ['lake', '--wfail', 'build'] for argv, _, _ in calls))
        self.assertEqual(len({root for _, root, _ in calls}), 10)
        self.assertEqual(len({log for _, _, log in calls}), 10)
        self.assertTrue(all(log.exists() for _, _, log in calls))
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
