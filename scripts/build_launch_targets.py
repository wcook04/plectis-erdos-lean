#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check changed modules first, then replay launch targets with durable diagnostics.

The same entry runs locally and in CI. A focused check never establishes full
coverage. Reports bind source and driver; logs survive failure and interruption.
The runner uses only the Python standard library and the selected checkout.
"""
from __future__ import annotations

import argparse
from collections import deque
from collections.abc import Callable, Sequence
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import sys
import time
import tomllib

ROOT = Path.cwd()
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
ERROR = re.compile(r'(?:^|\s)error: (.*?\.lean):(\d+):(\d+): (.*)')
HEARTBEAT_ENV = 'RELEASE_HEARTBEAT_SECONDS'
MODULE_BUDGET_ENV = 'RELEASE_MODULE_BUDGET_SECONDS'


def git(*args: str, root: Path = ROOT) -> str:
    return subprocess.check_output(['git', *args], cwd=root, text=True, timeout=30).strip()


def read_targets(path: Path) -> list[str]:
    with path.open('rb') as source:
        targets = tomllib.load(source).get('defaultTargets')
    if (not isinstance(targets, list) or not targets
            or any(not isinstance(t, str) or not MODULE.fullmatch(t) for t in targets)
            or len(set(targets)) != len(targets)):
        raise ValueError('defaultTargets must be a nonempty array of unique module/library names')
    return targets


def source_identity(root: Path) -> dict:
    # Track dirty source too: equal HEADs alone do not bind a local validation.
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root, timeout=30).split(b'\0')
    digest = hashlib.sha256()
    for raw in sorted(set(n for n in names if n)):
        name = os.fsdecode(raw)
        if name.startswith(('.lake/', '.ci-driver/')):
            continue
        if not (name.endswith('.lean') or name in ('lakefile.toml', 'lakefile.lean',
                                                   'lean-toolchain', 'lake-manifest.json')):
            continue
        path = root / name
        digest.update(raw + b'\0')
        digest.update(path.read_bytes() if path.is_file() else b'<deleted>')
        digest.update(b'\0')
    return {'commit': git('rev-parse', 'HEAD', root=root),
            'tree': git('rev-parse', 'HEAD^{tree}', root=root),
            'source_sha256': digest.hexdigest(),
            'toolchain': (root / 'lean-toolchain').read_text().strip(),
            'manifest_sha256': hashlib.sha256((root / 'lake-manifest.json').read_bytes()).hexdigest()}


def focused_targets(root: Path, base: str) -> list[str]:
    # PRs compare with their actual parent, including stacked PRs. On manual
    # dispatch the default main comparison catches stale branch-only modules.
    ancestor = git('merge-base', 'HEAD', base, root=root)
    names = subprocess.check_output(['git', 'diff', '--name-only', '-z', '--diff-filter=ACMR',
                                     ancestor, '--', '*.lean'], cwd=root, timeout=30).split(b'\0')
    with (root / 'lakefile.toml').open('rb') as source:
        libraries = tomllib.load(source).get('lean_lib', [])
    roots = sorted({str(row.get('srcDir', '.')) for row in libraries}, key=len, reverse=True)
    modules = {}
    for raw in names:
        if not raw:
            continue
        path = Path(os.fsdecode(raw))
        if not (root/path).is_file():
            continue
        for source_root in roots:
            try:
                candidate = path.relative_to(source_root).with_suffix('').as_posix().replace('/', '.')
            except ValueError:
                continue
            if MODULE.fullmatch(candidate):
                modules[candidate] = root/path
                break
    # Dependencies among changed files go first. This catches a failed imported
    # module before spending time building its changed downstream consumers.
    ordered, active, done = [], set(), set()
    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError('changed-module import cycle: '+module)
        active.add(module)
        text = modules[module].read_text()
        for imported in re.findall(r'^import\s+([\w.]+)', text, re.M):
            if imported in modules:
                visit(imported)
        active.remove(module); done.add(module); ordered.append(module)
    for module in sorted(modules):
        visit(module)
    return ordered


def make_plan(root: Path, base: str | None, focus: Sequence[str], focused_only: bool) -> dict:
    targets = read_targets(root/'lakefile.toml')
    changed = focused_targets(root, base) if base else []
    priority = list(dict.fromkeys([*focus, *changed]))
    if any(not MODULE.fullmatch(t) for t in priority):
        raise ValueError('invalid focused module name')
    if focused_only and not priority:
        raise ValueError('focused-only validation requires at least one module')
    phases = [{'target': t, 'phase': 'focused'} for t in priority]
    if not focused_only:
        phases += [{'target': t, 'phase': 'launch'} for t in targets if t not in priority]
    return {'schema_version': 2, 'source': source_identity(root),
            'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope': 'focused' if focused_only else 'full',
            'baseline': base, 'default_targets': targets, 'targets': phases}


def save_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    temporary.replace(path)


def owned_modules(ps_output: str, ancestor: int) -> list[tuple[int, int, str]]:
    """Only compiler descendants of this Lake process; never touch other builds."""
    processes = {}
    for line in ps_output.splitlines():
        parts = line.split(maxsplit=3)
        if len(parts) == 4 and all(p.isdigit() for p in parts[:3]):
            processes[int(parts[0])] = (int(parts[1]), int(parts[2]), parts[3])
    descendants = {ancestor}
    while True:
        expanded = descendants | {pid for pid, (parent, _, _) in processes.items() if parent in descendants}
        if expanded == descendants:
            break
        descendants = expanded
    result = []
    for pid in descendants:
        if pid not in processes:
            continue
        _, elapsed, command = processes[pid]
        args = command.split()
        if args and Path(args[0]).name == 'lean':
            source = next((arg for arg in args[1:] if arg.endswith('.lean')), None)
            if source:
                result.append((pid, elapsed, source))
    return result


def stop_process(process: subprocess.Popen) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=3)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=3)
    # A shell may exit before its compiler descendants. Clean up the entire
    # group even when waiting for the direct child returned successfully.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def annotation(message: str) -> str:
    return message.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')


def run_build(argv: list[str], *, root: Path, log: Path, timeout: float,
              heartbeat: float, module_budget: float, progress: Callable,
              max_log_bytes: int = 128*1024*1024) -> dict:
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    errors, tail = [], deque(maxlen=30)
    total = 0; pending = b''; reason = None; next_beat = started+heartbeat
    process = subprocess.Popen(argv, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    def consume(line):
        text = line.decode('utf-8', errors='replace').rstrip()
        tail.append(text[-2000:])
        if (match := ERROR.search(text)) and len(errors) < 20:
            errors.append({'file': match[1], 'line': int(match[2]),
                           'column': int(match[3]), 'message': match[4]})
            location=annotation(match[1]).replace(',', '%2C').replace(':', '%3A')
            print(f'::error file={location},line={match[2]},col={match[3]}::'+annotation(match[4]), flush=True)
            progress(errors)
        elif (text.startswith('error:') or 'Some required targets logged failures' in text):
            print(text[-2000:], flush=True)
    try:
        with gzip.open(log, 'wb') as output:
            while selector.get_map():
                now = time.monotonic()
                if now-started > timeout:
                    reason = 'target_timeout'; break
                if now >= next_beat:
                    print(f'[build] {argv[-1]} still running after {int(now-started)}s; log {log}', flush=True)
                    try:
                        table = subprocess.run(['ps','-eo','pid=,ppid=,etimes=,args='],
                                               capture_output=True,text=True,timeout=5,check=False)
                        modules = owned_modules(table.stdout, process.pid)
                    except (OSError, subprocess.TimeoutExpired):
                        modules = []
                    overdue = [source for _, elapsed, source in modules if elapsed > module_budget]
                    if overdue:
                        errors += [{'message': 'module budget exceeded', 'file': p} for p in overdue]
                        reason = 'module_timeout'; progress(errors); break
                    next_beat = now+heartbeat
                for key, _ in selector.select(timeout=min(0.2, max(0.01, timeout-(now-started)))):
                    chunk = os.read(key.fd, 65536)
                    if not chunk:
                        selector.unregister(key.fileobj); continue
                    total += len(chunk)
                    if total > max_log_bytes:
                        reason = 'log_budget_exceeded'; break
                    output.write(chunk); pending += chunk
                    while b'\n' in pending:
                        line, pending = pending.split(b'\n', 1); consume(line)
                    if len(pending) > 65536:
                        consume(pending[:65536]); pending = b''
                if reason:
                    break
            if pending:
                consume(pending)
        if reason:
            stop_process(process)
        code = process.wait(timeout=max(1, timeout-(time.monotonic()-started)))
    except (KeyboardInterrupt, InterruptedError):
        stop_process(process); code = 130; reason = 'cancelled'
    except BaseException:
        stop_process(process)
        raise
    finally:
        selector.close()
        process.stdout.close()
    return {'returncode': code, 'reason': reason, 'errors': errors,
            'seconds': round(time.monotonic()-started, 3), 'log': str(log),
            'log_bytes': min(total,max_log_bytes), 'tail': list(tail) if code or reason else []}


def build_targets(targets: Sequence[str], report_path: Path, run: Callable | None = None,
                  metadata: dict | None = None, *, plan: dict | None = None,
                  root: Path = ROOT, keep_going: bool = True, target_budget: float | None = None,
                  total_budget: float = 18000, heartbeat: float = 60,
                  module_budget: float = 3600) -> int:
    if not targets or any(not MODULE.fullmatch(t) for t in targets):
        raise ValueError('refusing empty or invalid target replay')
    rows = [dict(target=t, status='not-attempted', returncode=None,
                 phase=(plan['targets'][i]['phase'] if plan else 'launch')) for i,t in enumerate(targets)]
    report = {'schema_version': 2, 'status': 'running', 'targets': rows,
              'budgets': {'target_seconds': target_budget, 'total_seconds': total_budget,
                          'module_seconds': module_budget}}
    if plan:
        report['plan'] = plan
    if metadata is not None:
        report['release_gate'] = metadata
    save_report(report_path,report)
    deadline = time.monotonic()+total_budget
    interrupted = False
    try:
        for i,row in enumerate(rows):
            if time.monotonic() >= deadline:
                row.update(status='incomplete', reason='run_timeout'); interrupted=True; break
            row['status']='running'; save_report(report_path,report)
            print(f"[build] {i+1}/{len(rows)} {row['phase']}: {row['target']}",flush=True)
            try:
                if run is not None:
                    result={'returncode':run(['lake','build',row['target']],check=False).returncode}
                else:
                    def progress(errors):
                        row['errors']=list(errors); save_report(report_path,report)
                    result=run_build(['lake','build',row['target']],root=root,
                                     log=report_path.parent/'convenience-logs'/f'{i:03d}-{row["target"]}.log.gz',
                                     timeout=min(target_budget or total_budget,deadline-time.monotonic()),heartbeat=heartbeat,
                                     module_budget=module_budget,progress=progress)
                if result.get('reason') == 'target_timeout' and (target_budget is None or time.monotonic() >= deadline):
                    result['reason'] = 'run_timeout'
                row.update(result)
                if result.get('reason'):
                    print('::error::'+annotation(f"{row['target']}: {result['reason']} after {result.get('seconds', 0)}s; see retained compiler log"), flush=True)
                code=result['returncode']
                interrupted=bool(result.get('reason')) or code<0 or code in (130,137,143)
                row['status']='incomplete' if interrupted else ('pass' if code==0 else 'fail')
            except (OSError,KeyboardInterrupt,InterruptedError,subprocess.TimeoutExpired) as error:
                row.update(status='incomplete',error=type(error).__name__+': '+str(error)); interrupted=True
            save_report(report_path,report)
            if interrupted or (row['status']!='pass' and (not keep_going or row['phase']=='focused')):
                break
        if plan and source_identity(root)!=plan['source']:
            report['source_changed']=True; interrupted=True
    finally:
        report['status']=('incomplete' if interrupted else
                          ('pass' if all(r['status']=='pass' for r in rows) else 'fail'))
        if report['status']=='pass' and plan and plan['scope']=='focused':
            report['status']='focused-pass'
        save_report(report_path,report)
        lines=['## Lean Convenience', '', f"Result: **{report['status']}**.", '',
               '| Target | Phase | Result | Reason |', '| --- | --- | --- | --- |']
        lines += [f"| `{r['target']}` | {r['phase']} | {r['status']} | {r.get('reason') or ''} |" for r in rows]
        summary='\n'.join(lines)+'\n';print(summary,flush=True)
        if destination:=os.environ.get('GITHUB_STEP_SUMMARY'):
            with open(destination,'a') as output:output.write(summary)
    return 2 if interrupted else (0 if report['status'] in ('pass','focused-pass') else 1)


def positive(value: str) -> float:
    number=float(value)
    if not 0<number<=86400:
        raise argparse.ArgumentTypeError('budget must be positive and no more than one day')
    return number


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository',type=Path,default=Path.cwd())
    parser.add_argument('--lakefile',type=Path)
    parser.add_argument('--report',type=Path,default=Path('.lake/convenience-target-report.json'))
    parser.add_argument('--changed-from',help='PR base or comparison ref; merge-base is used')
    parser.add_argument('--focus',action='append',default=[])
    parser.add_argument('--focused-only',action='store_true')
    parser.add_argument('--keep-going',action='store_true',help='collect later launch-target failures too')
    parser.add_argument('--plan',action='store_true',help='write admission plan without invoking Lean')
    parser.add_argument('--target-budget',type=positive,help='optional aggregate target cap; by default only module and whole-run budgets apply')
    parser.add_argument('--total-budget',type=positive,default=18000)
    parser.add_argument('--heartbeat',type=positive,default=os.environ.get(HEARTBEAT_ENV,'60'))
    parser.add_argument('--module-budget',type=positive,default=os.environ.get(MODULE_BUDGET_ENV,'3600'))
    args=parser.parse_args()
    root=args.repository.resolve();report=args.report if args.report.is_absolute() else root/args.report
    previous=signal.signal(signal.SIGTERM,lambda *_: (_ for _ in ()).throw(InterruptedError('SIGTERM')))
    try:
        report.unlink(missing_ok=True)
        # --lakefile remains supported by existing local callers/tests.
        if args.lakefile:
            targets=read_targets(args.lakefile)
            return build_targets(targets,report,root=root,keep_going=args.keep_going)
        plan=make_plan(root,args.changed_from,args.focus,args.focused_only)
        if args.plan:
            save_report(report,{'status':'planned','plan':plan});print(json.dumps(plan,indent=2));return 0
        return build_targets([row['target'] for row in plan['targets']],report,plan=plan,
                             root=root,keep_going=args.keep_going,target_budget=args.target_budget,
                             total_budget=args.total_budget,heartbeat=args.heartbeat,module_budget=args.module_budget)
    except (OSError,ValueError,subprocess.SubprocessError,InterruptedError) as error:
        save_report(report,{'schema_version':2,'status':'incomplete','error':str(error)})
        print(f'::error::{annotation(str(error))}',file=sys.stderr);return 2
    finally:
        signal.signal(signal.SIGTERM,previous)


if __name__=='__main__':
    raise SystemExit(main())
