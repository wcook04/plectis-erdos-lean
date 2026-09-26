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
        self.assertFalse(self.report.exists())

    def test_report_write_failure_does_not_start_build(self):
        fake_run = unittest.mock.Mock()
        with patch.object(runner, 'save_report', side_effect=OSError('read-only')):
            with self.assertRaises(OSError):
                runner.build_targets(['First'], self.report, fake_run)
        fake_run.assert_not_called()


class ModuleWatchdogTests(unittest.TestCase):
    PS = ('  101   7300 /home/r/.elan/toolchains/v/bin/lean /w/Erdos249257/Slow.lean -R ./. -o x.olean\n'
          '  102     40 lean Solutions/Fast.lean\n'
          '  103   9000 /usr/bin/python3 scripts/run.py Slow.lean\n'
          '  104   9000 lake build Solutions\n'
          'garbage line\n')

    def test_only_lean_compiles_are_reported(self):
        self.assertEqual(runner.running_lean_modules(self.PS),
                         [(101, 7300, '/w/Erdos249257/Slow.lean'), (102, 40, 'Solutions/Fast.lean')])

    def test_over_budget_module_is_stopped_once_and_named(self):
        watchdog = runner.ModuleWatchdog(interval=1, budget=3600)
        listing = subprocess.CompletedProcess([], 0, stdout=self.PS)
        with patch.object(runner.subprocess, 'run', return_value=listing), \
                patch.object(runner.os, 'kill') as kill, \
                contextlib.redirect_stdout(io.StringIO()) as out:
            watchdog.poll()
            watchdog.poll()
        kill.assert_called_once_with(101, runner.signal.SIGKILL)
        self.assertEqual(watchdog.killed, ['/w/Erdos249257/Slow.lean'])
        self.assertIn('::error file=/w/Erdos249257/Slow.lean::', out.getvalue())
        self.assertIn('still compiling Solutions/Fast.lean after 40s', out.getvalue())

    def test_zero_budget_only_reports(self):
        watchdog = runner.ModuleWatchdog(interval=1, budget=0)
        listing = subprocess.CompletedProcess([], 0, stdout=self.PS)
        with patch.object(runner.subprocess, 'run', return_value=listing), \
                patch.object(runner.os, 'kill') as kill, \
                contextlib.redirect_stdout(io.StringIO()):
            watchdog.poll()
        kill.assert_not_called()

    def test_stopped_module_fails_a_target_that_lake_passed(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        report = Path(directory.name) / 'report.json'
        stub = runner.ModuleWatchdog(interval=1, budget=1)
        stub.killed = ['Slow.lean']
        with patch.object(runner, 'start_watchdog', return_value=stub), \
                patch.dict(os.environ, {'GITHUB_STEP_SUMMARY': str(Path(directory.name) / 's.md')}), \
                contextlib.redirect_stdout(io.StringIO()):
            code = runner.build_targets(['Only'], report,
                                        lambda argv, check: subprocess.CompletedProcess(argv, 0))
        row = json.loads(report.read_text())['targets'][0]
        self.assertEqual((code, row['status'], row['over_budget_modules']), (1, 'fail', ['Slow.lean']))

    def test_watchdog_is_off_without_the_environment(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertIsNone(runner.start_watchdog())


if __name__ == '__main__':
    unittest.main()
