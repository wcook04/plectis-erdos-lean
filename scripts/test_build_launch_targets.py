# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise the runner without a Lean install or network access."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import build_launch_targets as runner
import convenience_ci as ci


class LaunchReplayTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.report = self.root / 'report.json'
        self.summary = self.root / 'summary.md'
        self.env = patch.dict(os.environ, {'GITHUB_STEP_SUMMARY': str(self.summary)})
        self.env.start()
        self.addCleanup(self.env.stop)

    def replay(self, outcomes):
        calls = []
        sequence = iter(outcomes)
        def fake_run(argv, *, check):
            self.assertFalse(check)
            calls.append(argv)
            result = next(sequence)
            if isinstance(result, BaseException):
                raise result
            return subprocess.CompletedProcess(argv, result)
        with contextlib.redirect_stdout(io.StringIO()):
            code = runner.build_targets(['First', 'Second', 'Third'], self.report, fake_run)
        return code, calls, json.loads(self.report.read_text())

    def test_success_attempts_every_target_in_order(self):
        code, calls, report = self.replay([0, 0, 0])
        self.assertEqual(code, 0)
        self.assertEqual(calls, [['lake', 'build', t] for t in ['First', 'Second', 'Third']])
        self.assertEqual(report['status'], 'pass')
        self.assertTrue(all(r['status'] == 'pass' for r in report['targets']))

    def test_early_failure_does_not_hide_later_targets(self):
        code, calls, report = self.replay([1, 0, 0])
        self.assertEqual(code, 1)
        self.assertEqual(len(calls), 3)
        self.assertEqual([r['status'] for r in report['targets']], ['fail', 'pass', 'pass'])
        self.assertIn('**fail**', self.summary.read_text())

    def test_multiple_failures_are_all_reported(self):
        code, calls, report = self.replay([1, 2, 0])
        self.assertEqual(code, 1)
        self.assertEqual(len(calls), 3)
        self.assertEqual([r['returncode'] for r in report['targets']], [1, 2, 0])

    def test_missing_executable_fails_closed(self):
        code, calls, report = self.replay([FileNotFoundError('lake')])
        self.assertEqual(code, 2)
        self.assertEqual(len(calls), 1)
        self.assertEqual(report['status'], 'incomplete')
        self.assertEqual(report['targets'][1]['status'], 'not-attempted')

    def test_interrupt_stops_and_cannot_pass(self):
        code, calls, report = self.replay([0, KeyboardInterrupt()])
        self.assertEqual(code, 2)
        self.assertEqual(len(calls), 2)
        self.assertEqual(report['status'], 'incomplete')

    def test_signal_and_shell_cancellation_codes_stop(self):
        for signal in [-9, -15, 130, 137, 143]:
            with self.subTest(signal=signal):
                code, calls, report = self.replay([signal])
                self.assertEqual(code, 2)
                self.assertEqual(len(calls), 1)
                self.assertEqual(report['status'], 'incomplete')

    def test_empty_direct_replay_is_rejected(self):
        with self.assertRaises(ValueError):
            runner.build_targets([], self.report)

    def test_toml_parser_uses_real_array_and_preserves_order(self):
        config = self.root / 'lakefile.toml'
        config.write_text("# defaultTargets = [\"Wrong\"]\ndefaultTargets = [\n'First',\n'Second',\n]\n")
        self.assertEqual(runner.read_targets(config), ['First', 'Second'])

    def test_invalid_target_arrays_are_rejected(self):
        config = self.root / 'lakefile.toml'
        for content in ['name="x"', 'defaultTargets=[]', 'defaultTargets="x"',
                        'defaultTargets=[1]', 'defaultTargets=[""]',
                        'defaultTargets=["--help"]', 'defaultTargets=["x","x"]']:
            with self.subTest(content=content):
                config.write_text(content)
                with self.assertRaises(ValueError):
                    runner.read_targets(config)

    def test_running_report_is_written_before_subprocess(self):
        def inspect(argv, *, check):
            report = json.loads(self.report.read_text())
            self.assertEqual(report['status'], 'running')
            self.assertEqual(report['targets'][0]['status'], 'running')
            return subprocess.CompletedProcess(argv, 0)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(runner.build_targets(['First'], self.report, inspect), 0)

    def test_bad_configuration_removes_stale_success(self):
        self.report.write_text('{"status":"pass"}')
        config = self.root / 'lakefile.toml'
        config.write_text('defaultTargets=[]')
        with patch('sys.argv', ['runner', '--lakefile', str(config), '--report', str(self.report)]):
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(runner.main(), 2)
        self.assertEqual(json.loads(self.report.read_text())['status'],'incomplete')

    def test_report_write_failure_does_not_start_build(self):
        fake_run = unittest.mock.Mock()
        with patch.object(runner, 'save_report', side_effect=OSError('read-only')):
            with self.assertRaises(OSError):
                runner.build_targets(['First'], self.report, fake_run)
        fake_run.assert_not_called()


class ProcessAndPlanTests(unittest.TestCase):
    def setUp(self):
        # These tests deliberately emit proof errors and failed summaries.
        # Keep them out of the hosting workflow's diagnostics and job summary.
        self.output = io.StringIO()
        capture = contextlib.redirect_stdout(self.output)
        capture.__enter__()
        self.addCleanup(capture.__exit__, None, None, None)
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        env = patch.dict(os.environ, {'GITHUB_STEP_SUMMARY': str(Path(directory.name)/'summary')})
        env.start()
        self.addCleanup(env.stop)

    def test_watchdog_only_sees_this_builds_descendants(self):
        listing = "10 1 300 lake build X\n11 10 200 /bin/lean X.lean\n12 1 999 /bin/lean Other.lean\n13 11 40 /bin/lean Child.lean\n"
        self.assertEqual(runner.owned_modules(listing,10),[(11,200,'X.lean'),(13,40,'Child.lean')])

    def test_real_failure_has_source_error_and_compressed_log(self):
        import gzip
        with tempfile.TemporaryDirectory() as tmp:
            log=Path(tmp)/'target.log.gz';errors=[]
            result=runner.run_build([__import__('sys').executable,'-c',
                "print('warning: harmless'); print('error: Demo.lean:8:3: unsolved goals'); raise SystemExit(1)"],
                root=Path(tmp),log=log,timeout=5,heartbeat=1,module_budget=5,progress=lambda x:errors.extend(x))
            self.assertEqual(result['returncode'],1)
            self.assertEqual(result['errors'][0]['file'],'Demo.lean')
            self.assertEqual(result['errors'][0]['line'],8)
            self.assertIn('warning: harmless',gzip.open(log,'rt').read())
            self.assertTrue(errors)

    def test_real_timeout_stops_process_and_preserves_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            result=runner.run_build([__import__('sys').executable,'-c',
                "import time; print('started',flush=True); time.sleep(20)"],root=Path(tmp),
                log=Path(tmp)/'timeout.gz',timeout=0.15,heartbeat=1,module_budget=5,progress=lambda _:None)
            self.assertEqual(result['reason'],'target_timeout')
            self.assertNotEqual(result['returncode'],0)
            self.assertLess(result['seconds'],5)

    def test_log_budget_is_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            result=runner.run_build([__import__('sys').executable,'-c',"print('x'*50000)"],
                root=Path(tmp),log=Path(tmp)/'big.gz',timeout=5,heartbeat=1,module_budget=5,
                progress=lambda _:None,max_log_bytes=500)
            self.assertEqual(result['reason'],'log_budget_exceeded')

    def test_fail_fast_keeps_unattempted_targets_visible(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'r.json';calls=[]
            def fail(argv,check):
                calls.append(argv);return subprocess.CompletedProcess(argv,1)
            self.assertEqual(runner.build_targets(['First','Second'],path,fail,keep_going=False),1)
            self.assertEqual(len(calls),1)
            self.assertEqual(json.loads(path.read_text())['targets'][1]['status'],'not-attempted')

    def test_aggregate_target_uses_remaining_run_budget_by_default(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'r.json'
            with patch.object(runner.time,'monotonic',return_value=100):
                with patch.object(runner,'run_build',return_value={'returncode':0}) as build:
                    self.assertEqual(runner.build_targets(['LargeLibrary'],path,total_budget=18000),0)
            self.assertEqual(build.call_args.kwargs['timeout'],18000)
            self.assertIsNone(json.loads(path.read_text())['budgets']['target_seconds'])

    def test_explicit_aggregate_cap_is_preserved(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'r.json'
            with patch.object(runner,'run_build',return_value={'returncode':-15,'reason':'target_timeout','seconds':30}) as build:
                self.assertEqual(runner.build_targets(['LargeLibrary'],path,target_budget=30),2)
            self.assertEqual(build.call_args.kwargs['timeout'],30)
            self.assertEqual(json.loads(path.read_text())['targets'][0]['reason'],'target_timeout')

    def test_remaining_run_limit_cannot_be_mislabeled_or_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'r.json'
            with patch.object(runner,'run_build',return_value={'returncode':-15,'reason':'target_timeout','seconds':3}):
                self.assertEqual(runner.build_targets(['LargeLibrary','Later'],path,total_budget=3),2)
            report=json.loads(path.read_text())
            self.assertEqual(report['targets'][0]['reason'],'run_timeout')
            self.assertEqual(report['targets'][1]['status'],'not-attempted')

    def test_changed_dependencies_precede_consumers_and_scope_remains_full(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            def git(*args):return subprocess.check_output(['git',*args],cwd=root,text=True).strip()
            git('init','-q');git('config','user.name','Test');git('config','user.email','test@example.invalid')
            (root/'lakefile.toml').write_text('defaultTargets=["Library"]\n[[lean_lib]]\nname="Library"\nsrcDir="lean"\nroots=["A","Z"]\n')
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0')
            (root/'lake-manifest.json').write_text('{}')
            git('add','.');git('commit','-qm','base');base=git('rev-parse','HEAD')
            (root/'lean').mkdir();(root/'lean/Z.lean').write_text('def z := 1\n')
            (root/'lean/A.lean').write_text('import Z\n')
            git('add','.');git('commit','-qm','modules')
            plan=runner.make_plan(root,base,[],False)
            self.assertEqual([r['target'] for r in plan['targets']],['Z','A','Library'])
            self.assertEqual(plan['scope'],'full')
            old=runner.source_identity(root);(root/'lean/Z.lean').write_text('def z := 2\n')
            self.assertNotEqual(old,runner.source_identity(root))
            with patch.object(runner,'source_identity',return_value=old):
                path=root/'r.json'
                plan=runner.make_plan(root,None,['Z'],True)
                code=runner.build_targets(['Z'],path,lambda argv,check:subprocess.CompletedProcess(argv,0),plan=plan,root=root)
                self.assertEqual(code,0)
                self.assertEqual(json.loads(path.read_text())['status'],'focused-pass')

    def test_source_drift_cannot_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            plan={'scope':'full','source':{'commit':'old'},'targets':[{'target':'X','phase':'focused'}]}
            path=Path(tmp)/'r.json'
            with patch.object(runner,'source_identity',return_value={'commit':'new'}):
                code=runner.build_targets(['X'],path,lambda argv,check:subprocess.CompletedProcess(argv,0),plan=plan)
            self.assertEqual(code,2)
            self.assertTrue(json.loads(path.read_text())['source_changed'])

    def test_workflow_admission_artifacts_and_cache_boundary(self):
        root=Path(__file__).resolve().parents[1]
        if 'workflow_call:' not in (root/'.github/workflows/lean.yml').read_text():
            from release_inventory import validate_workflow_contract
            self.assertEqual(validate_workflow_contract(root),'legacy_complete_defaults')
            return
        text=(Path(__file__).resolve().parents[1]/'.github/workflows/lean.yml').read_text()
        self.assertIn('needs: infrastructure',text)
        self.assertLess(text.index('--plan'),text.index('Restore the corpus build'))
        self.assertIn('use-github-cache: false',text)
        self.assertIn('steps.resolve.outputs.source_sha',text)
        self.assertIn('.ci-driver/scripts/build_launch_targets.py',text)
        self.assertIn('.lake/convenience-logs/*.log.gz',text)
        self.assertIn('include-hidden-files: true',text)
        self.assertNotIn('path: .lake\n',text)
        self.assertIn("steps.lean.outcome == 'success' && inputs.source_ref == ''",text)
        self.assertIn('convenience-v3-${{ github.ref }}-',text)
        self.assertIn('${{ github.run_id }}-${{ github.run_attempt }}',text)
        self.assertIn('branches-ignore: [main]',text)
        self.assertNotIn('subprocess.run(["lake"',text)

    def test_release_gate_shares_the_runner_and_retains_its_audit(self):
        root=Path(__file__).resolve().parents[1]
        if 'workflow_call:' not in (root/'.github/workflows/lean.yml').read_text():
            from release_inventory import validate_workflow_contract
            self.assertEqual(validate_workflow_contract(root),'legacy_complete_defaults')
            return
        root=Path(__file__).resolve().parents[1]/'.github/workflows'
        release=(root/'release-gate.yml').read_text()
        shared=(root/'lean.yml').read_text()
        self.assertIn('uses: ./.github/workflows/lean.yml',release)
        self.assertIn('audit_publication: true',release)
        self.assertIn('group: lean-release-${{ github.ref }}',release)
        self.assertIn('cancel-in-progress: true',release)
        self.assertNotIn('subprocess.run',release)
        self.assertIn('workflow_call:',shared)
        self.assertIn('check_axiom_budget.py --run-palomar --json',shared)
        self.assertIn('name: palomar-publication-audit',shared)
        self.assertIn('group: lean-convenience-${{ github.workflow }}-',shared)
        self.assertLess(shared.index('id: compile'),shared.index('id: audit'))

    def test_real_signal_is_not_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            result=runner.run_build([__import__('sys').executable,'-c',
                'import os,signal; os.kill(os.getpid(),signal.SIGTERM)'], root=Path(tmp),
                log=Path(tmp)/'signal.gz',timeout=5,heartbeat=1,module_budget=5,progress=lambda _:None)
            self.assertEqual(result['returncode'],-15)

    def test_invalid_budgets_rejected(self):
        for value in ('0','-1','nan','inf','100000'):
            with self.assertRaises((ValueError,runner.argparse.ArgumentTypeError)):
                runner.positive(value)


class ChangedModuleOwnershipTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'user.email', 'test@example.invalid')
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0')
        (self.root/'lake-manifest.json').write_text('{}')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def plan(self, configuration, files):
        (self.root/'lakefile.toml').write_text(configuration)
        self.git('add', '.')
        self.git('commit', '-qm', 'base')
        base = self.git('rev-parse', 'HEAD')
        for name, body in files.items():
            path = self.root/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(body)
        self.git('add', '.')
        self.git('commit', '-qm', 'changed sources')
        return runner.make_plan(self.root, base, [], False)

    def test_outer_project_excludes_nested_projects_and_unclaimed_fixtures(self):
        plan = self.plan('defaultTargets=["Outer"]\n[[lean_lib]]\nname="Outer"\n', {
            'Outer/Z.lean': 'def z := 1\n',
            'Outer/A.lean': 'import Outer.Z\n',
            'verification/Other/lakefile.toml': 'name="other"\n',
            'verification/Other/lean/Outer/Z.lean': 'def z := 2\n',
            'fixtures/Outer/Z.lean': 'def z := 3\n',
            'OuterBackup/Z.lean': 'def z := 4\n',
        })
        self.assertEqual([row['target'] for row in plan['targets']], ['Outer.Z', 'Outer.A', 'Outer'])
        self.assertEqual({row['path'] for row in plan['excluded_changed_sources']}, {
            'verification/Other/lean/Outer/Z.lean', 'fixtures/Outer/Z.lean', 'OuterBackup/Z.lean'})
        self.assertTrue(all(row['reason'] == 'not_buildable_in_selected_project'
                            for row in plan['excluded_changed_sources']))
        self.assertEqual(plan['scope'], 'full')

    def test_package_and_library_source_dirs_custom_roots_and_extra_globs(self):
        plan = self.plan('defaultTargets=["Library"]\nsrcDir="src"\n[[lean_lib]]\n'
                         'name="Library"\nsrcDir="proofs"\nroots=["Actual"]\n'
                         'globs=["Actual", "Extra.*", "Descendants.+", "Single"]\n', {
            'src/proofs/Actual/Z.lean': 'def z := 1\n',
            'src/proofs/Actual/A.lean': 'import Actual.Z\n',
            'src/proofs/Extra.lean': 'def e := 1\n',
            'src/proofs/Extra/Child.lean': 'def e := 2\n',
            'src/proofs/Descendants/Child.lean': 'def d := 1\n',
            'src/proofs/Single.lean': 'def s := 1\n',
            'src/proofs/Single/Child.lean': 'def s := 2\n',
            'src/proofs/Descendants.lean': 'def d := 2\n',
            'src/Actual/Wrong.lean': 'def w := 1\n',
        })
        focused = [row['target'] for row in plan['targets'] if row['phase'] == 'focused']
        self.assertEqual(focused, ['Actual.Z', 'Actual.A', 'Descendants.Child', 'Extra', 'Extra.Child', 'Single'])
        self.assertEqual({row['path'] for row in plan['excluded_changed_sources']}, {
            'src/proofs/Single/Child.lean', 'src/proofs/Descendants.lean', 'src/Actual/Wrong.lean'})
        self.assertEqual(plan['targets'][-1], {'target': 'Library', 'phase': 'launch'})

    def test_unselected_root_and_shadowed_source_are_not_build_targets(self):
        plan = self.plan('defaultTargets=["Later"]\n[[lean_lib]]\nname="Earlier"\n'
                         'srcDir="old"\nroots=["Shared"]\n[[lean_lib]]\n'
                         'name="Later"\nsrcDir="new"\nroots=["Shared", "Unselected"]\n'
                         'globs=["Shared"]\n', {
            'old/Shared/Changed.lean': 'def old := 1\n',
            'new/Shared/Changed.lean': 'def current := 1\n',
            'new/Unselected/Child.lean': 'def unselected := 1\n',
        })
        self.assertEqual([row['target'] for row in plan['targets']], ['Shared.Changed', 'Later'])
        self.assertEqual({row['path'] for row in plan['excluded_changed_sources']}, {
            'old/Shared/Changed.lean', 'new/Unselected/Child.lean'})


class SetupBoundaryTests(unittest.TestCase):
    def test_named_and_abbreviated_refs_resolve_to_full_commit(self):
        for ref in ('abc1234', 'topic/change', 'v1.0', 'a'*40):
            api = unittest.mock.Mock(return_value=subprocess.CompletedProcess([], 0, 'b'*40+'\n', ''))
            self.assertEqual(ci.resolve_source('owner/repo', ref, api), 'b'*40)
            self.assertIn('repos/owner/repo/commits/'+ci.quote(ref, safe=''), api.call_args.args[0])
            self.assertEqual(api.call_args.kwargs['timeout'], 45)

    def test_bad_ref_and_api_failure_never_reach_checkout(self):
        for code, output in ((1, ''), (0, 'abc1234'), (0, 'null'), (0, 'bad\nsource_sha=evil')):
            api = unittest.mock.Mock(return_value=subprocess.CompletedProcess([], code, output, ''))
            with self.assertRaises(ValueError):
                ci.resolve_source('owner/repo', 'unknown', api)
        api = unittest.mock.Mock()
        with self.assertRaises(ValueError):
            ci.resolve_source('owner/repo', 'bad\nref', api)
        api.assert_not_called()
        with self.assertRaises(subprocess.TimeoutExpired):
            ci.resolve_source('owner/repo', 'main', unittest.mock.Mock(side_effect=subprocess.TimeoutExpired('gh',45)))

    def test_setup_failure_has_diagnostics_without_target_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            report = ci.finalize({'status':'incomplete','requested_source':'abc1234'},
                                 Path(tmp)/'absent.json', {'source':{'outcome':'failure'}})
            self.assertEqual(report['status'], 'incomplete')
            self.assertEqual(report['requested_source'], 'abc1234')
            self.assertEqual(report['incomplete_steps'], {'source':'failure'})
            self.assertEqual(report['reason'], 'setup_did_not_reach_build')

    def test_setup_failure_cannot_leave_planned_or_stale_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'r.json'
            for status in ('planned', 'running', 'pass', 'focused-pass'):
                path.write_text(json.dumps({'status':status,'plan':{}}))
                report = ci.finalize({},path,{'lean':{'outcome':'failure'}})
                self.assertEqual(report['status'],'incomplete')
            path.write_text('{"status":"fail"}')
            self.assertEqual(ci.finalize({},path,{'compile':{'outcome':'failure'}})['status'],'fail')
            path.write_text('{"status":"pass","plan":{}}')
            self.assertEqual(ci.finalize({},path,{'compile':{'outcome':'success'}})['status'],'pass')

    def test_negative_tests_do_not_pollute_hosting_workflow(self):
        with tempfile.TemporaryDirectory() as tmp:
            summary = Path(tmp)/'host-summary'
            summary.write_text('real summary\n')
            env = dict(os.environ, GITHUB_STEP_SUMMARY=str(summary))
            result = subprocess.run([__import__('sys').executable,'-m','unittest',
                'test_build_launch_targets.ProcessAndPlanTests'], cwd=Path(__file__).parent,
                env=env, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertNotIn('::error',result.stdout+result.stderr)
            self.assertEqual(summary.read_text(),'real summary\n')

    def test_artifact_exists_before_any_checkout(self):
        root=Path(__file__).resolve().parents[1]
        if 'workflow_call:' not in (root/'.github/workflows/lean.yml').read_text():
            from release_inventory import validate_workflow_contract
            self.assertEqual(validate_workflow_contract(root),'legacy_complete_defaults')
            return
        workflow=(Path(__file__).resolve().parents[1]/'.github/workflows/lean.yml').read_text()
        build=workflow[workflow.index('  build:'):]
        self.assertLess(build.index('Initialize setup diagnostics'),build.index('uses: actions/checkout'))
        self.assertLess(build.index('convenience_ci.py resolve'),build.index('name: Check out the resolved source'))
        self.assertIn('${{ runner.temp }}/convenience-target-report.json',build)
        self.assertIn('lake-package-directory: source',build)
        self.assertIn('Publication audit requires the complete launch set',build)
        self.assertIn('if [[ "$FOCUSED_ONLY" == true ]]; then args+=(--focused-only); fi',build)


if __name__ == '__main__':
    unittest.main()
