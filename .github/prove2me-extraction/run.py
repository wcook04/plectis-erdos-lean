#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the pinned Prove2Me extractors on a separately checked-out source commit.

The module list is an input inventory. Declaration dependencies and source
positions come only from the two official Lean extractors.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import signal
import math
from datetime import datetime, timezone
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = json.loads((HERE / "manifest.json").read_text())
OFFICIAL_RAW = "https://raw.githubusercontent.com/prove2me/prove2me_workspace"
MAX_LOG_BYTES = 8_000_000
MAX_ARTIFACT_BYTES = 400_000_000
MIN_FREE_DISK_BYTES = 2 * 1024**3


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def replace_once(text: str, before: str, after: str) -> str:
    check(text.count(before) == 1, f"official extractor edit anchor changed: {before!r}")
    return text.replace(before, after)


def save_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def disk_guard(source: Path, out: Path, phase: str) -> None:
    usage = shutil.disk_usage(source)
    receipt = out / "resource_receipt.json"
    history = json.loads(receipt.read_text()) if receipt.exists() else {"samples": []}
    sample = {"at": datetime.now(timezone.utc).isoformat(), "phase": phase,
              "total_bytes": usage.total, "used_bytes": usage.used,
              "free_bytes": usage.free, "minimum_free_bytes": MIN_FREE_DISK_BYTES}
    history["samples"].append(sample)
    save_json(receipt, history)
    check(usage.free >= MIN_FREE_DISK_BYTES,
          f"runner disk below 2 GiB before {phase}; see {receipt}")


def select_request() -> None:
    request = json.loads((HERE / "request.json").read_text())
    check(set(request) == {"problem", "stage"}, "unexpected request keys")
    problem, stage = request["problem"], request["stage"]
    check(problem in MANIFEST["cases"] and stage in {"graph", "full"},
          "unsupported pinned extraction request")
    selected = {"problem": problem, "stage": stage,
                "source_commit": MANIFEST["cases"][problem]["source_commit"]}
    if "GITHUB_OUTPUT" in os.environ:
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
            for key, value in selected.items():
                output.write(f"{key}={value}\n")
    print(json.dumps(selected, sort_keys=True))


def source_pin(source: Path, case: dict) -> None:
    head = subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    check(head == case["source_commit"], f"source commit changed: {head}")
    for path in ("lean-toolchain", "lake-manifest.json"):
        blob = subprocess.check_output(
            ["git", "-C", str(source), "show", f"{head}:{path}"])
        check((source / path).read_bytes() == blob, f"pinned {path} bytes changed")
    check((source / "lean-toolchain").read_text().strip() == case["toolchain"],
          "Lean toolchain changed")
    lake = json.loads((source / "lake-manifest.json").read_text())
    mathlib = [p for p in lake["packages"] if p["name"] == "mathlib"]
    check(len(mathlib) == 1 and mathlib[0]["rev"] == case["mathlib_rev"],
          "Mathlib revision changed")
    rows = case["module_rows"]
    check(len(rows) == len({row["module"] for row in rows}), "duplicate input module")
    for row in rows:
        path = module_path(row["module"])
        check(digest((source / path).read_bytes()) == row["sha256"],
              f"pinned module bytes changed: {path}")
    roots = {row["module"] for row in rows}
    check(all(root in roots for root in case["root_modules"]),
          "a root module is missing from the audited input inventory")


def prepare(source: Path, out: Path, problem: str, case: dict) -> None:
    source_pin(source, case)
    out.mkdir(parents=True, exist_ok=True)
    disk_guard(source, out, "before toolchain setup")
    official = {}
    for name, expected in MANIFEST["extractor_sha256"].items():
        url = f"{OFFICIAL_RAW}/{MANIFEST['official_workspace_commit']}/scripts/{name}"
        with urllib.request.urlopen(url, timeout=30) as response:
            data = response.read()
        check(digest(data) == expected, f"official extractor hash changed: {name}")
        official[name] = data
    graph = official["extract_decl_graph.lean"].decode()
    imports = "".join(f"import {root}\n" for root in case["root_modules"])
    graph = replace_once(graph, "import SumSquares\n", imports)
    if len(case["project_prefixes"]) == 1:
        prefix = case["project_prefixes"][0]
        replacement = (f"let projPrefix := `{prefix}\n"
                       "  let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m\n")
    else:
        prefixes = ", ".join("`" + prefix for prefix in case["project_prefixes"])
        replacement = (f"let projPrefixes : Array Name := #[{prefixes}]\n"
                       "  let isProj : Name → Bool := fun m => projPrefixes.any (fun p => p.isPrefixOf m)\n")
    graph = replace_once(
        graph,
        "let projPrefix := `SumSquares\n  let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m\n",
        replacement,
    )
    check(digest(graph.encode()) == case["prepared_graph_sha256"],
          "prepared Stage 1 script differs from audited input")
    (source / "extract_decl_graph.lean").write_text(graph)
    (source / "extract_sketch_info.lean").write_bytes(official["extract_sketch_info.lean"])
    save_json(out / "input_receipt.json", {
        "schema": "prove2me_remote_extraction_input_v1",
        "problem": problem,
        "source_commit": case["source_commit"],
        "toolchain": case["toolchain"],
        "mathlib_rev": case["mathlib_rev"],
        "official_workspace_commit": MANIFEST["official_workspace_commit"],
        "official_script_sha256": MANIFEST["extractor_sha256"],
        "prepared_graph_sha256": digest(graph.encode()),
        "module_count": len(case["module_rows"]),
        "root_modules": case["root_modules"],
        "selected_declarations": case["selected_declarations"],
    })
    print(f"Pinned {problem} input, {len(case['module_rows'])} modules; Lean has not run.")


# One bounded budget for every source module, including namespace projections.
# Names and source byte sizes are not proxies for elaboration cost.
STAGE2_MODULE_SECONDS = 1800


def remaining_budget(requested: float) -> float:
    deadline = os.environ.get('P2M_EXTRACTION_DEADLINE_EPOCH')
    if deadline:
        value = float(deadline)
        check(math.isfinite(value), 'invalid extraction deadline')
        requested = min(requested, value - time.time())
    check(requested > 0, 'extraction execution deadline exhausted; reserve time for diagnostics')
    return requested


def bounded_process(command, source, stdout, stderr, timeout):
    """Kill owned descendants as well as Lake on timeout or interruption."""
    budget = remaining_budget(timeout)
    process = subprocess.Popen(command, cwd=source, stdout=stdout, stderr=stderr,
                               start_new_session=True, env={**os.environ, 'LEAN_NUM_THREADS':'1'})
    try:
        return process.wait(timeout=budget)
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass
        # The direct process may have exited while a descendant ignored TERM.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        raise


def trim_log(path):
    if path.exists() and path.stat().st_size > MAX_LOG_BYTES:
        with path.open('rb') as stream:
            stream.seek(-MAX_LOG_BYTES, os.SEEK_END)
            tail = stream.read()
        path.write_bytes(b'[earlier output omitted]\n' + tail)


def run_logged(command: list[str], source: Path, log: Path, timeout: int) -> None:
    print('Running', ' '.join(command), flush=True)
    try:
        with log.open('w') as stream:
            code = bounded_process(command, source, stream, subprocess.STDOUT, timeout)
    finally:
        trim_log(log)
    if code:
        print(log.read_text()[-8000:], file=sys.stderr)
        raise RuntimeError(f'command exited {code}; see {log}')


def build(source: Path, out: Path, case: dict) -> None:
    source_pin(source, case)
    for root in case["root_modules"]:
        disk_guard(source, out, f"before build {root}")
        run_logged(["lake", "build", root], source,
                   out / f"build_{root}.log", timeout=14400)
        disk_guard(source, out, f"after build {root}")


def jsonl_rows(path: Path) -> list[dict]:
    check(path.is_file() and path.stat().st_size <= 100_000_000,
          f"missing or oversized extractor output: {path}")
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def stage1(source: Path, out: Path, case: dict) -> None:
    source_pin(source, case)
    disk_guard(source, out, "before Stage 1")
    check(digest((source / "extract_decl_graph.lean").read_bytes()) ==
          case["prepared_graph_sha256"], "Stage 1 script changed")
    run_logged(["lake", "env", "lean", "extract_decl_graph.lean"], source,
               out / "stage1.log", timeout=1200)
    disk_guard(source, out, "after Stage 1")
    graph = source / "decl_graph.jsonl"
    rows = jsonl_rows(graph)
    for selected in case["selected_declarations"]:
        matches = [row for row in rows if row.get("name") == selected["name"]]
        check(len(matches) == 1 and matches[0].get("module") == selected["module"],
              f"selected declaration absent or ambiguous: {selected['name']}")
    check(all(any(row.get("module", "") == prefix or
                  row.get("module", "").startswith(prefix + ".") for prefix in
                  case["project_prefixes"]) for row in rows),
          "declaration graph contains an unreviewed project prefix")
    (out / "decl_graph.jsonl").write_bytes(graph.read_bytes())
    save_json(out / "stage1_receipt.json", {
        "schema": "prove2me_remote_stage1_v1",
        "source_commit": case["source_commit"],
        "row_count": len(rows),
        "selected_declarations": case["selected_declarations"],
        "decl_graph_sha256": digest(graph.read_bytes()),
    })
    print(f"Stage 1: {len(rows)} declaration rows, all selected names present.")


def stage2(source: Path, out: Path, case: dict) -> None:
    source_pin(source, case)
    check((out / "stage1_receipt.json").is_file(), "Stage 1 must finish first")
    check(digest((source / "extract_sketch_info.lean").read_bytes()) ==
          MANIFEST["extractor_sha256"]["extract_sketch_info.lean"],
          "Stage 2 script changed")
    target = out / "sketch_info"
    target.mkdir(exist_ok=True)
    # A partial receipt remains incomplete. Reuse requires exact inputs and hashes;
    # a timeout can never be turned into successful extraction by cached files.
    progress_path = out/'stage2_progress.json'
    binding = {'source_commit':case['source_commit'], 'driver_sha256':digest(Path(__file__).read_bytes()),
               'module_rows':case['module_rows'],
               'extractor_sha256': MANIFEST['extractor_sha256']['extract_sketch_info.lean']}
    old = json.loads(progress_path.read_text()) if progress_path.exists() else {}
    reusable = {row['module']:row for row in old.get('outputs',[]) if row.get('status')=='pass'} if old.get('binding')==binding else {}
    progress = {'schema':'prove2me_stage2_progress_v1','status':'incomplete','binding':binding,
                'module_budget_seconds':STAGE2_MODULE_SECONDS,
                'outputs':[{'module':row['module'],'status':'not_attempted'} for row in case['module_rows']]}
    save_json(progress_path, progress)
    # No stale successful final receipt survives a new incomplete attempt.
    (out/'stage2_receipt.json').unlink(missing_ok=True)
    results = []
    for index, row in enumerate(case['module_rows']):
        relative = module_path(row['module'])
        output = target/(row['module']+'.jsonl')
        error = target/(row['module']+'.stderr.log')
        prior = reusable.get(row['module'])
        item = progress['outputs'][index]
        started = time.monotonic()
        try:
            disk_guard(source,out,f'before Stage 2 {relative}')
            if prior and output.is_file() and digest(output.read_bytes())==prior['sha256']:
                rows=jsonl_rows(output)
                check(len(rows)==prior['row_count'],'cached extraction row count changed')
                item.update(prior, reused=True)
            else:
                budget=remaining_budget(STAGE2_MODULE_SECONDS)
                item.update(status='running',budget_seconds=budget)
                save_json(progress_path,progress)
                print('Stage 2',relative,f'timeout={budget:.0f}s',flush=True)
                with output.open('w') as stdout,error.open('w') as stderr:
                    code=bounded_process(['lake','env','lean','--run','extract_sketch_info.lean',str(relative)],source,stdout,stderr,budget)
                check(code==0,f'Stage 2 failed on {relative}: exit {code}; see {error.name}')
                rows=jsonl_rows(output)
                item.update(status='pass',sha256=digest(output.read_bytes()),row_count=len(rows),reused=False)
            results.append({key:item[key] for key in ('module','sha256','row_count')})
            size=sum(path.stat().st_size for path in out.rglob('*') if path.is_file())
            check(size<=MAX_ARTIFACT_BYTES,'extraction artifact exceeds 400 MB ceiling')
        except BaseException as exc:
            item.update(status='timeout' if isinstance(exc,subprocess.TimeoutExpired) else 'fail',error=str(exc))
            progress['failed_module']=row['module']
            raise
        finally:
            trim_log(error)
            item['elapsed_seconds']=round(time.monotonic()-started,3)
            save_json(progress_path,progress)
    progress['status']='pass'
    save_json(progress_path,progress)
    save_json(out / "stage2_receipt.json", {
        "schema": "prove2me_remote_stage2_v1",
        "source_commit": case["source_commit"],
        "module_count": len(results),
        "outputs": results,
    })
    print(f"Stage 2: {len(results)} module outputs.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["select", "prepare", "build", "stage1", "stage2"])
    parser.add_argument("--problem", choices=["257", "243", "249", "68", "269", "1049", "251", "1041", "257_overlay", "249_remainder"])
    parser.add_argument("--source", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.phase == "select":
        select_request()
        return
    if args.problem is None or args.source is None or args.out is None:
        parser.error("--problem, --source and --out are required")
    source, out = args.source.resolve(), args.out.resolve()
    case = MANIFEST["cases"][args.problem]
    if args.phase == "prepare":
        prepare(source, out, args.problem, case)
    elif args.phase == "build":
        build(source, out, case)
    elif args.phase == "stage1":
        stage1(source, out, case)
    else:
        stage2(source, out, case)


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(InterruptedError("SIGTERM")))
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        # Diagnostic artifact and original nonzero result survive every phase.
        args=sys.argv
        out=Path(args[args.index('--out')+1]) if '--out' in args else Path('output')
        save_json(out/'failure.json', {'status':'fail','phase':args[1] if len(args)>1 else None,
                  'command':args, 'error':str(error),'control_commit':os.environ.get('GITHUB_SHA')})
        message=str(error).replace('%','%25').replace('\n','%0A').replace('\r','%0D')
        print('::error title=Pinned extraction::'+message,file=sys.stderr)
        raise SystemExit(1)
