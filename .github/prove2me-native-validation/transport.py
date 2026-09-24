#!/usr/bin/env python3
"""Package and run exact-byte, read-only remote Prove2Me Lean validation.

The runner deliberately creates a new path-rebound plan. Its receipt records
both plan hashes; the original reviewed plan is never rewritten or passed off
as the runtime plan. No Prove2Me credential or API operation belongs here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path, PurePosixPath


SCHEMA = "prove2me_remote_native_bundle_v1"
PENDING_SCHEMA = "prove2me_remote_native_pending_bundle_v1"
RESULT_SCHEMA = "prove2me_remote_native_validation_run_v1"
HEX = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
SCRIPTS = (
    "preflight.py", "cache_preflight.py", "run_stage_build.py",
    "run_type_axiom_audit.py", "assemble_production_receipt.py",
)
MAX_FILE = 100 * 1024 * 1024
MAX_TOTAL = 2 * 1024 * 1024 * 1024


class TransportError(ValueError):
    pass


def require(value: bool, message: str) -> None:
    if not value:
        raise TransportError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def no_duplicates(pairs: list[tuple[str, object]]) -> dict:
    result: dict = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(raw: bytes) -> dict:
    value = json.loads(raw, object_pairs_hook=no_duplicates)
    require(isinstance(value, dict), "expected JSON object")
    return value


def encode(value: dict) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def safe_name(name: str) -> None:
    parts = PurePosixPath(name)
    require(name == str(parts) and not parts.is_absolute() and
            all(part not in ("", ".", "..") for part in parts.parts) and
            "\\" not in name, f"unsafe bundle path: {name!r}")


def module_path(module: str, suffix: str) -> str:
    require(isinstance(module, str) and bool(MODULE.fullmatch(module)),
            f"invalid module name: {module!r}")
    return "/".join(module.split(".")) + suffix


def source_path(raw: str) -> Path:
    require(isinstance(raw, str) and bool(raw), "missing source path")
    return Path(raw).resolve()


def add_file(files: dict[str, bytes], name: str, path: Path) -> None:
    safe_name(name)
    require(name not in files and path.is_file() and not path.is_symlink(),
            f"missing, duplicate or symlinked input: {name}")
    data = path.read_bytes()
    require(len(data) <= MAX_FILE, f"input too large: {name}")
    files[name] = data


def write_bundle(out: Path, files: dict[str, bytes], manifest: dict) -> None:
    require(not out.exists() and not out.is_symlink(), "bundle output exists")
    require(sum(map(len, files.values())) <= MAX_TOTAL, "bundle exceeds size limit")
    out.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out, "x", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(files.items()):
            safe_name(name)
            info = zipfile.ZipInfo(name, date_time=(2020, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
        info = zipfile.ZipInfo("manifest.json", date_time=(2020, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, encode(manifest))


def original_preflight(plan: Path, module_map: Path, validation_dir: Path) -> dict:
    sys.path.insert(0, str(validation_dir.resolve()))
    try:
        from preflight import check  # type: ignore
        return check(plan, module_map)
    finally:
        sys.path.pop(0)


def prepare(plan_path: Path, map_path: Path, graph_path: Path,
            gate_path: Path, out: Path, validation_dir: Path) -> dict:
    require(not out.exists() and not out.is_symlink(), "bundle output exists")
    for path in (plan_path, map_path, graph_path, gate_path):
        require(path.is_file() and not path.is_symlink(), f"missing input: {path}")
    offline = original_preflight(plan_path, map_path, validation_dir)
    plan, mapping = load_json(plan_path.read_bytes()), load_json(map_path.read_bytes())
    graph, gate = load_json(graph_path.read_bytes()), load_json(gate_path.read_bytes())
    require(gate.get("status") == "source_import_cache_candidate" and
            graph.get("source_commit") == gate.get("source_commit") and
            graph.get("cache_checkout_commit") == gate.get("cache_checkout_commit"),
            "graph and source/cache gate are not aligned")
    require(isinstance(gate.get("modules"), list) and
            gate.get("module_count") == len(gate["modules"]) and
            set(mapping) == {row.get("module") for row in gate["modules"]},
            "source gate inventory differs from generated module map")
    roots = graph.get("lean_library_roots")
    require(isinstance(roots, list) and bool(roots) and
            all(isinstance(root, str) and Path(root).is_absolute() for root in roots),
            "graph has no absolute Lean library roots")
    old_cache = Path(roots[0]).parents[3]
    require(Path(roots[0]) == old_cache / ".lake/build/lib/lean" and
            all(Path(root).is_relative_to(old_cache) for root in roots),
            "graph library roots do not share one cache checkout")
    files: dict[str, bytes] = {}
    for label, path in (("plan", plan_path), ("module_map", map_path),
                        ("graph_config", graph_path), ("source_gate", gate_path)):
        add_file(files, f"original/{label}.json", path)
    add_file(files, "original/stage1.jsonl", source_path(plan["authority"]["stage1"]))
    add_file(files, "original/payloads.json", plan_path.parent / "payloads.json")
    for row in gate["modules"]:
        module = row["module"]
        require(mapping[module]["sha256"] == row["sha256"] and
                Path(mapping[module]["source"]).is_absolute(),
                f"source gate/source map mismatch: {module}")
        add_file(files, "original/source/" + module_path(module, ".lean"),
                 source_path(mapping[module]["source"]))
        add_file(files, "original/stage2/" + module + ".jsonl",
                 source_path(mapping[module]["stage2"]))
    for action in plan["actions"]:
        relative = action["file"]
        safe_name(relative)
        add_file(files, "original/stage/" + relative, plan_path.parent / relative)
    for script in SCRIPTS:
        add_file(files, "code/validation/" + script, validation_dir / script)
    add_file(files, "code/transport.py", Path(__file__).resolve())
    require(sum(map(len, files.values())) <= MAX_TOTAL, "bundle exceeds size limit")
    manifest = {
        "schema": SCHEMA,
        "status": "offline_inputs_verified_not_lean_validated",
        "source_commit": gate["source_commit"],
        "cache_checkout_commit": gate["cache_checkout_commit"],
        "toolchain": gate["toolchain"],
        "mathlib_rev": gate["mathlib_rev"],
        "module_count": len(mapping),
        "action_count": len(plan["actions"]),
        "original_plan_sha256": offline["plan_sha256"],
        "original_module_map_sha256": offline["module_map_sha256"],
        "original_stage1_sha256": offline["stage1_sha256"],
        "original_payloads_sha256": plan["payloads_sha256"],
        "actions": [{"kind": a["kind"], "name": a["name"],
                     "file": a["file"], "sha256": a["sha256"]}
                    for a in plan["actions"]],
        "files": {name: {"sha256": sha(data), "size": len(data)}
                  for name, data in sorted(files.items())},
    }
    write_bundle(out, files, manifest)
    return {"bundle": str(out), "bundle_sha256": file_sha(out),
            "original_plan_sha256": offline["plan_sha256"],
            "action_count": len(plan["actions"]), "module_count": len(mapping)}


def prepare_pending(plan_path: Path, map_path: Path, artifact: Path,
                    control_manifest: Path, source: Path, problem: str,
                    out: Path, validation_dir: Path) -> dict:
    """Package exact source and generated actions while the cache remains pending."""
    require(problem in ("243", "257"), "unsupported problem")
    require(map_path.name == "module_map.json" and
            all(path.is_file() and not path.is_symlink() for path in
                (plan_path, map_path, artifact, control_manifest)),
            "missing or symlinked pending input")
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    try:
        from derive_runtime_inputs import verify_imported  # type: ignore
        case, imported_receipt, mapping = verify_imported(
            artifact, source, control_manifest, map_path.parent, problem)
    finally:
        sys.path.pop(0)
    offline = original_preflight(plan_path, map_path, validation_dir)
    plan = load_json(plan_path.read_bytes())
    case_rows = {row["module"]: row["sha256"] for row in case["module_rows"]}
    require(set(mapping) == set(case_rows) == set(plan["authority"]["stage2"])
            and all(mapping[module]["sha256"] == case_rows[module]
                    for module in mapping),
            "generated plan and reviewed case inventories differ")
    files: dict[str, bytes] = {}
    for label, path in (("plan", plan_path), ("module_map", map_path)):
        add_file(files, f"original/{label}.json", path)
    add_file(files, "original/stage1.jsonl", source_path(plan["authority"]["stage1"]))
    add_file(files, "original/payloads.json", plan_path.parent / "payloads.json")
    add_file(files, "original/extraction_artifact.zip", artifact)
    add_file(files, "original/extraction_manifest.json", control_manifest)
    add_file(files, "original/import_receipt.json", map_path.parent / "import_receipt.json")
    for module in sorted(mapping):
        add_file(files, "original/source/" + module_path(module, ".lean"),
                 source_path(mapping[module]["source"]))
        add_file(files, "original/stage2/" + module + ".jsonl",
                 source_path(mapping[module]["stage2"]))
        require(sha(files["original/source/" + module_path(module, ".lean")])
                == case_rows[module], f"source bytes differ: {module}")
    for action in plan["actions"]:
        safe_name(action["file"])
        add_file(files, "original/stage/" + action["file"],
                 plan_path.parent / action["file"])
        require(sha(files["original/stage/" + action["file"]]) == action["sha256"],
                f"staged action bytes differ: {action['file']}")
    for script in SCRIPTS:
        add_file(files, "code/validation/" + script, validation_dir / script)
    native = Path(__file__).resolve().parent
    add_file(files, "code/remote_import/import_artifact.py",
             native.parent / "remote_import/import_artifact.py")
    add_file(files, "code/remote_validation/derive_runtime_inputs.py",
             native / "derive_runtime_inputs.py")
    add_file(files, "code/transport.py", Path(__file__).resolve())
    manifest = {
        "schema": PENDING_SCHEMA,
        "status": "source_only_pending_cache",
        "problem": problem,
        "source_commit": case["source_commit"],
        "toolchain": case["toolchain"],
        "mathlib_rev": case["mathlib_rev"],
        "module_count": len(mapping),
        "action_count": len(plan["actions"]),
        "original_plan_sha256": offline["plan_sha256"],
        "original_module_map_sha256": offline["module_map_sha256"],
        "original_stage1_sha256": offline["stage1_sha256"],
        "original_payloads_sha256": plan["payloads_sha256"],
        "artifact_sha256": sha(files["original/extraction_artifact.zip"]),
        "control_manifest_sha256": sha(files["original/extraction_manifest.json"]),
        "import_receipt_sha256": sha(files["original/import_receipt.json"]),
        "actions": [{"kind": action["kind"], "name": action["name"],
                     "file": action["file"], "sha256": action["sha256"]}
                    for action in plan["actions"]],
        "files": {name: {"sha256": sha(data), "size": len(data)}
                  for name, data in sorted(files.items())},
    }
    require(imported_receipt["module_count"] == manifest["module_count"],
            "verified imported count differs from bundle")
    write_bundle(out, files, manifest)
    return {"bundle": str(out), "bundle_sha256": file_sha(out),
            "status": "source_only_pending_cache", "problem": problem,
            "original_plan_sha256": offline["plan_sha256"],
            "action_count": len(plan["actions"]), "module_count": len(mapping)}


def verify_bundle(bundle: Path, expected_sha: str) -> tuple[dict, dict[str, bytes]]:
    require(bool(HEX.fullmatch(expected_sha)), "invalid expected bundle SHA-256")
    require(bundle.is_file() and file_sha(bundle) == expected_sha, "bundle SHA-256 mismatch")
    with zipfile.ZipFile(bundle) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)) and "manifest.json" in names,
                "duplicate or missing bundle entries")
        for info in archive.infolist():
            safe_name(info.filename)
            mode = info.external_attr >> 16
            require(not info.is_dir() and (mode & 0o170000) in (0, 0o100000) and
                    info.file_size <= MAX_FILE, f"unsafe archive entry: {info.filename}")
        require(sum(info.file_size for info in archive.infolist()) <= MAX_TOTAL,
                "bundle expanded size exceeds limit")
        manifest = load_json(archive.read("manifest.json"))
        require(manifest.get("schema") in (SCHEMA, PENDING_SCHEMA) and
                isinstance(manifest.get("files"), dict)
                and set(names) == set(manifest["files"]) | {"manifest.json"},
                "bundle inventory differs from manifest")
        files: dict[str, bytes] = {}
        for name, pin in manifest["files"].items():
            safe_name(name)
            data = archive.read(name)
            require(isinstance(pin, dict) and pin.get("size") == len(data) and
                    pin.get("sha256") == sha(data), f"bundle entry changed: {name}")
            files[name] = data
    require(files["code/transport.py"] == Path(__file__).read_bytes(),
            "running transport code differs from reviewed bundle")
    for script in SCRIPTS:
        require("code/validation/" + script in files,
                f"missing validation code: {script}")
    if manifest["schema"] == PENDING_SCHEMA:
        require(manifest.get("status") == "source_only_pending_cache" and
                all(name in files for name in (
                    "original/extraction_artifact.zip", "original/extraction_manifest.json",
                    "original/import_receipt.json", "code/remote_import/import_artifact.py",
                    "code/remote_validation/derive_runtime_inputs.py")),
                "pending bundle lacks reviewed extraction or verifier")
    return manifest, files


def git_head(path: Path) -> str:
    return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                          check=True, capture_output=True, text=True,
                          timeout=10).stdout.strip()


def materialize(manifest: dict, files: dict[str, bytes], out: Path,
                source_checkout: Path, cache_checkout: Path,
                lean_binary: Path) -> tuple[dict, dict[str, Path]]:
    """Build a separately named runtime package with a strict, recorded path map."""
    source_checkout, cache_checkout = source_checkout.resolve(), cache_checkout.resolve()
    lean_binary = lean_binary.resolve()
    require(git_head(source_checkout) == manifest["source_commit"],
            "source checkout is not at the pinned source commit")
    require(lean_binary.is_file(), "Lean binary is missing")
    plan = load_json(files["original/plan.json"])
    mapping = load_json(files["original/module_map.json"])
    graph = load_json(files["original/graph_config.json"])
    gate = load_json(files["original/source_gate.json"])
    payloads = load_json(files["original/payloads.json"])
    require(sha(files["original/plan.json"]) == manifest["original_plan_sha256"] and
            sha(files["original/module_map.json"]) == manifest["original_module_map_sha256"] and
            sha(files["original/stage1.jsonl"]) == manifest["original_stage1_sha256"] and
            sha(files["original/payloads.json"]) == manifest["original_payloads_sha256"] and
            plan["payloads_sha256"] == manifest["original_payloads_sha256"] and
            plan["authority"]["stage1_sha256"] == manifest["original_stage1_sha256"],
            "original plan or extraction hashes differ from manifest")
    require(gate.get("source_commit") == graph.get("source_commit") == manifest["source_commit"]
            and gate.get("cache_checkout_commit") == graph.get("cache_checkout_commit")
            == manifest["cache_checkout_commit"]
            and gate.get("toolchain") == manifest["toolchain"]
            and gate.get("mathlib_rev") == manifest["mathlib_rev"]
            and gate.get("module_count") == manifest["module_count"]
            and len(plan["actions"]) == manifest["action_count"],
            "plan, graph, source gate or manifest pins differ")
    require(set(mapping) == set(plan["authority"]["stage2"]) ==
            {row["module"] for row in gate["modules"]},
            "module inventories differ")
    roots = graph.get("lean_library_roots")
    require(isinstance(roots, list) and bool(roots), "missing original library roots")
    old_cache = Path(roots[0]).parents[3]
    require(Path(roots[0]) == old_cache / ".lake/build/lib/lean" and
            all(Path(root).is_relative_to(old_cache) for root in roots),
            "original library roots leave their cache checkout")
    runtime = out / "runtime"
    stage = runtime / "stage"
    stage1 = runtime / "stage1.jsonl"
    stage1.parent.mkdir(parents=True)
    stage1.write_bytes(files["original/stage1.jsonl"])
    stage.mkdir()
    changes: list[dict[str, str]] = []

    def bind(pointer: str, old: str, new: str) -> None:
        changes.append({"json_pointer": pointer, "old": old, "new": new})

    old_stage1 = plan["authority"]["stage1"]
    plan["authority"]["stage1"] = str(stage1)
    bind("/plan/authority/stage1", old_stage1, str(stage1))
    source_gate_rows = {row["module"]: row for row in gate["modules"]}
    for module in sorted(mapping):
        source_rel = module_path(module, ".lean")
        source_bytes = files["original/source/" + source_rel]
        row, gate_row = mapping[module], source_gate_rows[module]
        pin = plan["authority"]["stage2"][module]
        require(row["sha256"] == gate_row["sha256"] == pin["source_sha256"]
                == sha(source_bytes) and gate_row["path"] == source_rel,
                f"source pin differs: {module}")
        for checkout in (source_checkout, cache_checkout):
            candidate = checkout / source_rel
            require(candidate.is_file() and not candidate.is_symlink() and
                    file_sha(candidate) == gate_row["sha256"],
                    f"source checkout/cache differs: {module}")
        new_source = str(cache_checkout / source_rel)
        old_source = row["source"]
        row["source"] = new_source
        bind(f"/module_map/{module}/source", old_source, new_source)
        stage2_bytes = files["original/stage2/" + module + ".jsonl"]
        require(sha(stage2_bytes) == pin["sha256"] and
                mapping[module]["stage2"] == pin["path"],
                f"Stage 2 extraction differs: {module}")
        new_stage2 = runtime / "stage2" / (module + ".jsonl")
        new_stage2.parent.mkdir(parents=True, exist_ok=True)
        new_stage2.write_bytes(stage2_bytes)
        old_stage2 = row["stage2"]
        row["stage2"] = str(new_stage2)
        pin["path"] = str(new_stage2)
        bind(f"/module_map/{module}/stage2", old_stage2, str(new_stage2))
        bind(f"/plan/authority/stage2/{module}/path", old_stage2, str(new_stage2))
    for name, payload in payloads.items():
        module = plan["validation"]["node_checks"][name]["original_import"]
        require(payload["source_file"] == load_json(files["original/module_map.json"])[module]["source"],
                f"payload source provenance differs: {name}")
        new_source = mapping[module]["source"]
        bind(f"/payloads/{name}/source_file", payload["source_file"], new_source)
        payload["source_file"] = new_source
    original_actions = manifest["actions"]
    require([{key: a[key] for key in ("kind", "name", "file", "sha256")}
             for a in plan["actions"]] == original_actions,
            "action inventory changed from reviewed bundle")
    for action in plan["actions"]:
        relative = action["file"]
        safe_name(relative)
        data = files["original/stage/" + relative]
        require(sha(data) == action["sha256"], f"action bytes differ: {relative}")
        dest = stage / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    payload_bytes = encode(payloads)
    (stage / "payloads.json").write_bytes(payload_bytes)
    bind("/plan/payloads_sha256", plan["payloads_sha256"], sha(payload_bytes))
    plan["payloads_sha256"] = sha(payload_bytes)
    graph_roots = [str(cache_checkout / Path(root).relative_to(old_cache)) for root in roots]
    bind("/graph/lean_binary", graph["lean_binary"], str(lean_binary))
    graph["lean_binary"] = str(lean_binary)
    for index, (old, new) in enumerate(zip(roots, graph_roots)):
        bind(f"/graph/lean_library_roots/{index}", old, new)
    graph["lean_library_roots"] = graph_roots
    paths = {"plan": stage / "plan.json", "module_map": runtime / "module_map.json",
             "graph": runtime / "graph_config.json", "gate": runtime / "source_gate.json"}
    paths["plan"].write_bytes(encode(plan))
    paths["module_map"].write_bytes(encode(mapping))
    paths["graph"].write_bytes(encode(graph))
    paths["gate"].write_bytes(files["original/source_gate.json"])
    for script in SCRIPTS:
        path = runtime / "validation" / script
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(files["code/validation/" + script])
    receipt = {
        "schema": "prove2me_remote_native_rebinding_v1",
        "status": "path_rebound_inputs_pending_lean",
        "original_plan_sha256": manifest["original_plan_sha256"],
        "runtime_plan_sha256": file_sha(paths["plan"]),
        "original_payloads_sha256": manifest["original_payloads_sha256"],
        "runtime_payloads_sha256": sha(payload_bytes),
        "original_module_map_sha256": manifest["original_module_map_sha256"],
        "runtime_module_map_sha256": file_sha(paths["module_map"]),
        "original_graph_sha256": sha(files["original/graph_config.json"]),
        "runtime_graph_sha256": file_sha(paths["graph"]),
        "source_gate_sha256": file_sha(paths["gate"]),
        "action_sha256": {a["file"]: a["sha256"] for a in plan["actions"]},
        "source_commit": manifest["source_commit"],
        "source_checkout": str(source_checkout),
        "cache_checkout": str(cache_checkout),
        "lean_binary_sha256": file_sha(lean_binary),
        "path_changes": changes,
    }
    (out / "rebinding_receipt.json").write_bytes(encode(receipt))
    return receipt, paths


def run_step(name: str, command: list[str], out: Path,
             timeout: int) -> int:
    with (out / f"{name}.stdout.log").open("wb") as stdout, \
         (out / f"{name}.stderr.log").open("wb") as stderr:
        try:
            completed = subprocess.run(command, stdout=stdout, stderr=stderr,
                                       timeout=timeout, check=False)
            return completed.returncode
        except subprocess.TimeoutExpired:
            stderr.write(f"remote {name} exceeded {timeout} seconds\n".encode())
            return 124


def complete_pending(manifest: dict, files: dict[str, bytes], out: Path,
                     source_checkout: Path, cache_checkout: Path,
                     lean_binary: Path, result: dict, result_path: Path) -> tuple[Path, dict]:
    """Re-import and derive a real cache gate before producing a runnable bundle."""
    require(manifest.get("schema") == PENDING_SCHEMA and
            manifest.get("status") == "source_only_pending_cache",
            "expected source-only pending bundle")
    require(sha(files["original/extraction_artifact.zip"]) == manifest["artifact_sha256"]
            and sha(files["original/extraction_manifest.json"])
            == manifest["control_manifest_sha256"]
            and sha(files["original/import_receipt.json"])
            == manifest["import_receipt_sha256"],
            "pending extraction evidence differs from manifest")
    bootstrap = out / "pending_bootstrap"
    bootstrap.mkdir()
    artifact = bootstrap / "artifact.zip"
    control = bootstrap / "manifest.json"
    artifact.write_bytes(files["original/extraction_artifact.zip"])
    control.write_bytes(files["original/extraction_manifest.json"])
    code = bootstrap / "code"
    for label in ("remote_import/import_artifact.py",
                  "remote_validation/derive_runtime_inputs.py",
                  *("validation/" + script for script in SCRIPTS)):
        target = code / label
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(files["code/" + label])
    imported = out / "pending_imported"
    derived = out / "pending_derived"
    for name, command in (
        ("pending_import", [sys.executable,
                            str(code / "remote_import/import_artifact.py"),
                            "--artifact", str(artifact), "--source", str(source_checkout),
                            "--manifest", str(control), "--problem", manifest["problem"],
                            "--out", str(imported)]),
        ("pending_derive", [sys.executable,
                            str(code / "remote_validation/derive_runtime_inputs.py"),
                            "--artifact", str(artifact), "--imported", str(imported),
                            "--source", str(source_checkout), "--cache", str(cache_checkout),
                            "--manifest", str(control), "--lean-binary", str(lean_binary),
                            "--problem", manifest["problem"], "--out", str(derived)]),
    ):
        exit_code = run_step(name, command, out, 300)
        result["steps"].append({
            "name": name, "exit_code": exit_code,
            "stdout_sha256": file_sha(out / f"{name}.stdout.log"),
            "stderr_sha256": file_sha(out / f"{name}.stderr.log"),
        })
        result_path.write_bytes(encode(result))
        require(exit_code == 0, f"{name} gate failed with exit code {exit_code}")
    gate_bytes = (derived / "source_gate.json").read_bytes()
    graph_bytes = (derived / "graph_config.json").read_bytes()
    derivation_bytes = (derived / "derivation_receipt.json").read_bytes()
    gate, graph, derivation = (load_json(raw) for raw in
                               (gate_bytes, graph_bytes, derivation_bytes))
    original_map = load_json(files["original/module_map.json"])
    fresh_map = load_json((imported / "module_map.json").read_bytes())
    gate_rows = {row["module"]: row for row in gate["modules"]}
    require(gate.get("problem") == manifest["problem"] and
            gate.get("source_commit") == manifest["source_commit"] and
            gate.get("toolchain") == manifest["toolchain"] and
            gate.get("mathlib_rev") == manifest["mathlib_rev"] and
            gate.get("module_count") == manifest["module_count"] and
            set(gate_rows) == set(original_map) == set(fresh_map) and
            set(gate_rows) == set(load_json(files["original/plan.json"])
                                  ["authority"]["stage2"]) and
            graph.get("source_gate_sha256") == sha(gate_bytes) and
            derivation.get("source_gate_sha256") == sha(gate_bytes) and
            derivation.get("graph_config_sha256") == sha(graph_bytes) and
            derivation.get("lean_executed") is False and
            set(derivation.get("observed_olean_sha256", {})) == set(gate_rows) and
            (imported / "decl_graph.jsonl").read_bytes() == files["original/stage1.jsonl"],
            "runner derivation differs from reviewed pending inventory")
    for module, row in gate_rows.items():
        source_name = "original/source/" + module_path(module, ".lean")
        stage2_name = "original/stage2/" + module + ".jsonl"
        require(original_map[module]["sha256"] == fresh_map[module]["sha256"]
                == row["sha256"] == sha(files[source_name]) and
                Path(fresh_map[module]["stage2"]).read_bytes() == files[stage2_name],
                f"runner source or Stage 2 differs from reviewed bundle: {module}")
    completed_files = dict(files)
    completed_files["original/source_gate.json"] = gate_bytes
    completed_files["original/graph_config.json"] = graph_bytes
    completed_manifest = dict(manifest)
    completed_manifest.update({
        "schema": SCHEMA,
        "status": "runner_source_cache_verified_lean_pending",
        "cache_checkout_commit": gate["cache_checkout_commit"],
        "files": {name: {"sha256": sha(data), "size": len(data)}
                  for name, data in sorted(completed_files.items())},
    })
    completed_bundle = out / "completed_bundle.zip"
    write_bundle(completed_bundle, completed_files, completed_manifest)
    completion = {
        "schema": "prove2me_remote_pending_completion_v1",
        "status": "source_cache_verified_lean_pending",
        "problem": manifest["problem"],
        "source_commit": manifest["source_commit"],
        "cache_checkout_commit": gate["cache_checkout_commit"],
        "module_count": manifest["module_count"],
        "original_plan_sha256": manifest["original_plan_sha256"],
        "original_action_sha256": {row["file"]: row["sha256"]
                                   for row in manifest["actions"]},
        "original_bundle_sha256": result["bundle_sha256"],
        "completed_bundle_sha256": file_sha(completed_bundle),
        "fresh_import_receipt_sha256": file_sha(imported / "import_receipt.json"),
        "derivation_receipt_sha256": sha(derivation_bytes),
        "source_gate_sha256": sha(gate_bytes),
        "graph_config_sha256": sha(graph_bytes),
        "lean_executed": False,
    }
    (out / "pending_completion_receipt.json").write_bytes(encode(completion))
    return completed_bundle, completion


def run_pending(bundle: Path, expected_sha: str, source_checkout: Path,
                cache_checkout: Path, lean_binary: Path, out: Path,
                *, max_load: float, timeout_seconds: int) -> dict:
    """Complete a pending cache gate in CI, then use the existing native runner."""
    require(not out.exists() and not out.is_symlink(), "output exists")
    run_id, workflow_sha = os.environ.get("GITHUB_RUN_ID"), os.environ.get("GITHUB_SHA")
    require(os.environ.get("GITHUB_REPOSITORY") == "wcook04/plectis-erdos-lean"
            and isinstance(run_id, str) and run_id.isdecimal()
            and isinstance(workflow_sha, str) and
            bool(re.fullmatch(r"[0-9a-f]{40}", workflow_sha)),
            "missing or incorrect GitHub Actions provenance")
    manifest, files = verify_bundle(bundle, expected_sha)
    require(manifest.get("schema") == PENDING_SCHEMA, "run-pending requires pending bundle")
    out = out.resolve()
    out.mkdir(parents=True)
    result = {"schema": RESULT_SCHEMA, "status": "source_only_pending_cache",
              "bundle_sha256": expected_sha, "manifest_sha256": sha(encode(manifest)),
              "source_commit": manifest["source_commit"],
              "github_repository": "wcook04/plectis-erdos-lean",
              "github_run_id": run_id, "github_sha": workflow_sha,
              "github_ref": os.environ.get("GITHUB_REF"),
              "steps": [], "upload_allowed": False}
    result_path = out / "remote_validation_receipt.json"
    result_path.write_bytes(encode(result))
    try:
        completed_bundle, completion = complete_pending(
            manifest, files, out, source_checkout, cache_checkout, lean_binary,
            result, result_path)
        result["pending_completion_receipt_sha256"] = file_sha(
            out / "pending_completion_receipt.json")
        result["completed_bundle_sha256"] = completion["completed_bundle_sha256"]
        result_path.write_bytes(encode(result))
        validated = run(completed_bundle, completion["completed_bundle_sha256"],
                        source_checkout, cache_checkout, lean_binary,
                        out / "validated", max_load=max_load,
                        timeout_seconds=timeout_seconds)
        result["validated_run_receipt_sha256"] = file_sha(
            out / "validated/remote_validation_receipt.json")
        result["steps"].extend(validated["steps"])
        require(validated["status"] == "passed_remote_lean_pending_hosted_readback",
                "completed native validation failed")
        result["production_receipt_sha256"] = validated["production_receipt_sha256"]
        result["status"] = "passed_remote_lean_pending_hosted_readback"
    except (OSError, KeyError, TypeError, ValueError, subprocess.SubprocessError) as exc:
        result["status"] = "failed"
        result["error"] = str(exc)
    result_path.write_bytes(encode(result))
    return result


def run(bundle: Path, expected_sha: str, source_checkout: Path,
        cache_checkout: Path, lean_binary: Path, out: Path,
        *, max_load: float, timeout_seconds: int) -> dict:
    require(not out.exists() and not out.is_symlink(), "output exists")
    run_id, workflow_sha = os.environ.get("GITHUB_RUN_ID"), os.environ.get("GITHUB_SHA")
    require(os.environ.get("GITHUB_REPOSITORY") == "wcook04/plectis-erdos-lean"
            and isinstance(run_id, str) and run_id.isdecimal()
            and isinstance(workflow_sha, str) and
            bool(re.fullmatch(r"[0-9a-f]{40}", workflow_sha)),
            "missing or incorrect GitHub Actions provenance")
    manifest, files = verify_bundle(bundle, expected_sha)
    require(manifest.get("schema") == SCHEMA, "run requires completed bundle")
    out = out.resolve()
    out.mkdir(parents=True)
    result = {"schema": RESULT_SCHEMA, "status": "running",
              "bundle_sha256": expected_sha,
              "manifest_sha256": sha(encode(manifest)),
              "source_commit": manifest["source_commit"],
              "github_repository": "wcook04/plectis-erdos-lean",
              "github_run_id": run_id, "github_sha": workflow_sha,
              "github_ref": os.environ.get("GITHUB_REF"),
              "steps": [], "upload_allowed": False}
    result_path = out / "remote_validation_receipt.json"
    result_path.write_bytes(encode(result))
    try:
        rebinding, paths = materialize(manifest, files, out, source_checkout,
                                       cache_checkout, lean_binary)
        result["rebinding_receipt_sha256"] = file_sha(out / "rebinding_receipt.json")
        result["original_plan_sha256"] = rebinding["original_plan_sha256"]
        result["runtime_plan_sha256"] = rebinding["runtime_plan_sha256"]
        base = out / "runtime" / "validation"
        common = ["--plan", str(paths["plan"]), "--module-map", str(paths["module_map"])]
        graph_gate = ["--graph-config", str(paths["graph"]),
                      "--source-gate", str(paths["gate"])]
        offline = out / "offline_preflight.json"
        build = out / "build"
        audit = out / "audit"
        production = out / "production_validation.json"
        steps = (
            ("preflight", [sys.executable, str(base / "preflight.py"), *common,
                           "--receipt", str(offline)], 120),
            ("build", [sys.executable, str(base / "run_stage_build.py"), *common,
                       *graph_gate, "--out", str(build), "--max-load", str(max_load),
                       "--timeout-seconds", str(timeout_seconds)],
             max(3600, timeout_seconds * manifest["action_count"] + 600)),
            ("audit", [sys.executable, str(base / "run_type_axiom_audit.py"), *common,
                       "--build-receipt", str(build / "build_receipt.json"),
                       *graph_gate, "--out", str(audit), "--max-load", str(max_load),
                       "--timeout-seconds", str(timeout_seconds)],
             max(3600, timeout_seconds * (manifest["action_count"] + 2) + 600)),
            ("assembly", [sys.executable, str(base / "assemble_production_receipt.py"),
                          *common, "--build-receipt", str(build / "build_receipt.json"),
                          "--audit-receipt", str(audit / "audit_receipt.json"),
                          *graph_gate, "--out", str(production)], 180),
        )
        for name, command, timeout in steps:
            code = run_step(name, command, out, timeout)
            row = {"name": name, "exit_code": code,
                   "stdout_sha256": file_sha(out / f"{name}.stdout.log"),
                   "stderr_sha256": file_sha(out / f"{name}.stderr.log")}
            result["steps"].append(row)
            result_path.write_bytes(encode(result))
            require(code == 0, f"{name} gate failed with exit code {code}")
        receipt = load_json(production.read_bytes())
        require(receipt.get("schema") == "prove2me_native_validation_v1" and
                receipt.get("mode") == "production" and
                receipt.get("plan_sha256") == rebinding["runtime_plan_sha256"] and
                all(receipt.get(key) == "passed" for key in
                    ("stage_build", "type_diff", "axiom_audit")),
                "production validation receipt is incomplete")
        result["production_receipt_sha256"] = file_sha(production)
        result["evidence_sha256"] = {
            "offline_preflight": file_sha(offline),
            "build_receipt": file_sha(build / "build_receipt.json"),
            "audit_receipt": file_sha(audit / "audit_receipt.json"),
            "type_diff": file_sha(audit / "type-diff.json"),
            "axioms": file_sha(audit / "axioms.json"),
        }
        result["status"] = "passed_remote_lean_pending_hosted_readback"
    except (OSError, KeyError, TypeError, ValueError, subprocess.SubprocessError) as exc:
        result["status"] = "failed"
        result["error"] = str(exc)
    result_path.write_bytes(encode(result))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare", help="write a reviewed input bundle")
    for flag in ("plan", "module-map", "graph-config", "source-gate", "out"):
        prep.add_argument("--" + flag, type=Path, required=True)
    prep.add_argument("--validation-dir", type=Path,
                      default=Path(__file__).resolve().parents[1] / "validation")
    pending = sub.add_parser("prepare-pending", help="bundle pinned source inputs before cache build")
    for flag in ("plan", "module-map", "artifact", "manifest", "source", "out"):
        pending.add_argument("--" + flag, type=Path, required=True)
    pending.add_argument("--problem", choices=("243", "257"), required=True)
    pending.add_argument("--validation-dir", type=Path,
                         default=Path(__file__).resolve().parents[1] / "validation")
    remote = sub.add_parser("run", help="validate one bundle in a pinned CI checkout")
    for flag in ("bundle", "source-checkout", "cache-checkout", "lean-binary", "out"):
        remote.add_argument("--" + flag, type=Path, required=True)
    remote.add_argument("--bundle-sha256", required=True)
    remote.add_argument("--max-load", type=float, default=10.0)
    remote.add_argument("--timeout-seconds", type=int, default=1800)
    remote_pending = sub.add_parser("run-pending", help="complete cache gate then validate in CI")
    for flag in ("bundle", "source-checkout", "cache-checkout", "lean-binary", "out"):
        remote_pending.add_argument("--" + flag, type=Path, required=True)
    remote_pending.add_argument("--bundle-sha256", required=True)
    remote_pending.add_argument("--max-load", type=float, default=10.0)
    remote_pending.add_argument("--timeout-seconds", type=int, default=1800)
    args = parser.parse_args()
    try:
        if args.command == "prepare":
            result = prepare(args.plan, args.module_map, args.graph_config,
                             args.source_gate, args.out, args.validation_dir)
        elif args.command == "prepare-pending":
            result = prepare_pending(args.plan, args.module_map, args.artifact,
                                     args.manifest, args.source, args.problem,
                                     args.out, args.validation_dir)
        else:
            require(args.timeout_seconds > 0 and args.max_load > 0,
                    "invalid positive runtime limit")
            runner = run_pending if args.command == "run-pending" else run
            result = runner(args.bundle, args.bundle_sha256, args.source_checkout,
                            args.cache_checkout, args.lean_binary, args.out,
                            max_load=args.max_load, timeout_seconds=args.timeout_seconds)
    except (OSError, KeyError, TypeError, ValueError, zipfile.BadZipFile) as exc:
        parser.exit(1, f"remote native validation failed: {exc}\n")
    print(json.dumps(result, sort_keys=True))
    if result.get("status") == "failed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
