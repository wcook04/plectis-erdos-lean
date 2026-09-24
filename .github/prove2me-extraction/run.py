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
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


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


def run_logged(command: list[str], source: Path, log: Path, timeout: int) -> None:
    print("Running", " ".join(command), flush=True)
    with log.open("w") as stream:
        try:
            result = subprocess.run(command, cwd=source, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=timeout,
                                    check=False, env={**os.environ, "LEAN_NUM_THREADS": "1"})
        except subprocess.TimeoutExpired as exc:
            if log.stat().st_size > MAX_LOG_BYTES:
                with log.open("rb") as prior:
                    prior.seek(-MAX_LOG_BYTES, os.SEEK_END)
                    tail = prior.read()
                log.write_bytes(b"[earlier build output omitted]\n" + tail)
            raise RuntimeError(f"command exceeded {timeout}s; see {log}") from exc
    if log.stat().st_size > MAX_LOG_BYTES:
        with log.open("rb") as stream:
            stream.seek(-MAX_LOG_BYTES, os.SEEK_END)
            tail = stream.read()
        log.write_bytes(b"[earlier build output omitted]\n" + tail)
    if result.returncode:
        print(log.read_text()[-8000:], file=sys.stderr)
        raise RuntimeError(f"command exited {result.returncode}; see {log}")


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
    results = []
    for row in case["module_rows"]:
        relative = module_path(row["module"])
        disk_guard(source, out, f"before Stage 2 {relative}")
        name = row["module"] + ".jsonl"
        output = target / name
        error = target / (row["module"] + ".stderr.log")
        command = ["lake", "env", "lean", "--run", "extract_sketch_info.lean",
                   str(relative)]
        # The 886,933-byte CertificateKernel source reached the original 300 s
        # cap on run 36004062630, after Stage 1 had passed. Keep the longer
        # allowance specific to that reviewed source; other modules retain the
        # shorter failure bound.
        timeout = 1800 if row["module"] == "Erdos249257.CertificateKernel" else 300
        print("Stage 2", relative, f"timeout={timeout}s", flush=True)
        with output.open("w") as stdout, error.open("w") as stderr:
            try:
                result = subprocess.run(command, cwd=source, stdout=stdout,
                                        stderr=stderr, timeout=timeout, check=False,
                                        env={**os.environ, "LEAN_NUM_THREADS": "1"})
            except subprocess.TimeoutExpired as exc:
                raise RuntimeError(f"Stage 2 timed out on {relative}") from exc
        if result.returncode:
            print(error.read_text()[-8000:], file=sys.stderr)
            raise RuntimeError(f"Stage 2 failed on {relative}: {result.returncode}")
        if error.stat().st_size > MAX_LOG_BYTES:
            with error.open("rb") as stream:
                stream.seek(-MAX_LOG_BYTES, os.SEEK_END)
                tail = stream.read()
            error.write_bytes(b"[earlier stderr omitted]\n" + tail)
        rows = jsonl_rows(output)
        results.append({"module": row["module"], "sha256": digest(output.read_bytes()),
                        "row_count": len(rows)})
        size = sum(path.stat().st_size for path in out.rglob("*") if path.is_file())
        check(size <= MAX_ARTIFACT_BYTES, "extraction artifact exceeds 400 MB ceiling")
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
    parser.add_argument("--problem", choices=["257", "243"])
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
    main()
