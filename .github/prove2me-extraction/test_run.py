# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""No Lean or network: real process termination and exact checkpoint reuse."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import run as runner


class ExtractionTests(unittest.TestCase):
    def test_uniform_budget_survives_namespaces_and_deadline_exhaustion(self):
        self.assertEqual(runner.STAGE2_MODULE_SECONDS,1800)
        with patch.dict(os.environ,{'P2M_EXTRACTION_DEADLINE_EPOCH':str(time.time()+15)}):
            self.assertLessEqual(runner.remaining_budget(1800),15)
        with patch.dict(os.environ,{'P2M_EXTRACTION_DEADLINE_EPOCH':'0'}):
            with self.assertRaisesRegex(ValueError,'deadline exhausted'):
                runner.remaining_budget(1800)

    def test_partial_failure_resume_and_changed_output(self):
        with tempfile.TemporaryDirectory() as tmp,contextlib.redirect_stdout(io.StringIO()):
            root=Path(tmp);source=root/'source';out=root/'output';source.mkdir();out.mkdir()
            extractor=b'fixture';(source/'extract_sketch_info.lean').write_bytes(extractor)
            (out/'stage1_receipt.json').write_text('{}')
            names=['Erdos249257.CertificateKernel','P2M_Overlay.Erdos249257.CertificateKernel','Unrelated.Module']
            case={'source_commit':'exact-source','module_rows':[{'module':n,'sha256':'pinned-'+n} for n in names]}
            calls=[];fail=[True]
            def fake(command,source,stdout,stderr,timeout):
                calls.append((command[-1],timeout));stdout.write('{"fixture":true}\n')
                if fail[0] and len(calls)==2:
                    raise subprocess.TimeoutExpired(command,timeout)
                return 0
            manifest={'extractor_sha256':{'extract_sketch_info.lean':runner.digest(extractor)}}
            with patch.object(runner,'source_pin'),patch.object(runner,'disk_guard'),patch.object(runner,'MANIFEST',manifest),patch.object(runner,'bounded_process',side_effect=fake),patch.dict(os.environ,{'P2M_EXTRACTION_DEADLINE_EPOCH':str(time.time()+7200)}):
                with self.assertRaises(subprocess.TimeoutExpired):runner.stage2(source,out,case)
                report=json.loads((out/'stage2_progress.json').read_text())
                self.assertEqual([r['status'] for r in report['outputs']],['pass','timeout','not_attempted'])
                self.assertFalse((out/'stage2_receipt.json').exists())
                self.assertTrue(all(timeout==1800 for _,timeout in calls))
                fail[0]=False;calls.clear();runner.stage2(source,out,case)
                self.assertEqual(len(calls),2)
                report=json.loads((out/'stage2_receipt.json').read_text())
                self.assertEqual([r['module'] for r in report['outputs']],names)
                calls.clear();(out/'sketch_info'/f'{names[0]}.jsonl').write_text('corrupt')
                runner.stage2(source,out,case);self.assertEqual(len(calls),1)
                # Same artifact identity with different input pins cannot reuse any module.
                calls.clear();case['source_commit']='different-source';runner.stage2(source,out,case)
                self.assertEqual(len(calls),3)

    def test_timeout_kills_descendant_after_parent_exits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);pidfile=root/'pid';output=root/'log'
            child='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)'
            code='import subprocess,sys,time;from pathlib import Path;p=subprocess.Popen([sys.executable,"-c",'+repr(child)+']);Path('+repr(str(pidfile))+').write_text(str(p.pid));time.sleep(60)'
            with output.open('w') as log,patch.dict(os.environ,{'P2M_EXTRACTION_DEADLINE_EPOCH':str(time.time()+10)}):
                with self.assertRaises(subprocess.TimeoutExpired):
                    runner.bounded_process([sys.executable,'-c',code],root,log,log,0.5)
            pid=int(pidfile.read_text())
            observed=subprocess.run(['ps','-o','stat=','-p',str(pid)],capture_output=True,text=True).stdout.strip()
            self.assertTrue(not observed or observed.startswith('Z'),observed)

    def test_workflow_reserves_finalization_and_tests_before_setup(self):
        text=(Path(__file__).resolve().parents[1]/'workflows/prove2me-pinned-extraction.yml').read_text()
        self.assertIn('18600',text)
        self.assertLess(text.index('test_run.py'),text.index('uses: leanprover/lean-action'))
        self.assertIn("if: always()",text)
        self.assertIn('output/stage2_progress.json',text)


if __name__=='__main__':unittest.main()
