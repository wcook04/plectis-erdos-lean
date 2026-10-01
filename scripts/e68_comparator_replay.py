#!/usr/bin/env python3
"""Replay the exact E68 finite-denominator Comparator target on a hosted runner.

This runs no local fallback when the supported systemd sandbox is unavailable.
The receipt records the positive and deliberately mismatched negative run
separately; only both kernel acceptances plus the exact negative diagnostic pass.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from palomar_replay_shard import (
    SubprocessRunner, classify_comparator, comparator_argv, sandbox_preflight,
)


FAMILY = "ExternalVerification68FiniteDenominator"
TARGET = "Erdos249257.ExternalVerification68FiniteDenominator.full_finite_denominator_exclusion"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
MISMATCH = "Challenge and solution theorem statement do not match: '" + TARGET + "'"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_contract(root: Path) -> dict:
    binding = json.loads((root / FAMILY / "source_binding.json").read_text())
    if binding["selected_theorem"] != TARGET:
        raise ValueError("selected theorem drift")
    checked = {}
    for row in binding["source_modules"]:
        path = root / row["path"]
        actual = sha(path)
        if actual != row["sha256"]:
            raise ValueError("source closure drift: " + row["path"])
        checked[row["path"]] = actual
    for name, expected in binding["source_environment_sha256"].items():
        actual = sha(root / name)
        if actual != expected:
            raise ValueError("source environment drift: " + name)
        checked[name] = actual
    for name in ("Challenge.lean", "Solution.lean", "NegativeSolution.lean",
                 "AxiomAudit.lean", "comparator.json", "comparator-negative-mismatch.json",
                 "source_binding.json", "check_contract.py"):
        checked[f"{FAMILY}/{name}"] = sha(root / FAMILY / name)
    return {"binding_source_commit": binding["source_commit"], "sha256": checked}


def audit_axioms(output: str) -> list[str]:
    # Lean may wrap the list after its first axiom; keep the target and label
    # on one line, then consume only through that list's closing bracket.
    found = re.search(re.escape(TARGET) + r"[^\n]*depends on axioms:\s*\[([^\]]*)\]",
                      output)
    if found is None:
        raise ValueError("selected target #print axioms line absent or malformed")
    axioms = [item.strip() for item in found.group(1).split(",") if item.strip()]
    if len(axioms) != len(set(axioms)) or not set(axioms) <= ALLOWED_AXIOMS:
        raise ValueError("selected target has unexpected axioms: " + repr(axioms))
    return axioms


def run(args: argparse.Namespace) -> int:
    root = args.root.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    receipt = {
        "schema": "e68_comparator_independent_replay_v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repository_head": head,
        "expected_head": args.expected_head,
        "selected_theorem": TARGET,
        "github": {key: os.environ.get("GITHUB_" + key)
                   for key in ("RUN_ID", "RUN_ATTEMPT", "SHA", "REF")},
        "tool_revisions": {key: os.environ.get(key) for key in
                           ("COMPARATOR_REV", "LEAN4EXPORT_REV", "LANDRUN_REV", "NANODA_REV")},
        "toolchains": {"source": None, "comparator": None},
        "source": None,
        "sandbox_mode": None,
        "axioms": None,
        "stages": [],
        "raw_log_sha256": {},
        "positive": None,
        "negative": None,
        "passed": False,
        "failure": None,
    }
    runner = SubprocessRunner(cwd=root)

    def stage(label: str, argv: list[str] | None, *, lean: bool = False) -> dict:
        log = out / (label + ".log")
        result = runner(label, argv, log_path=log,
                        env={"LEAN_NUM_THREADS": "2"} if lean else None)
        row = {"name": label, "argv": argv, "process_exit": result["returncode"],
               "seconds": result["seconds"], "log": log.name,
               "log_sha256": sha(log) if log.exists() else None}
        receipt["stages"].append(row)
        if result["returncode"] != 0 and label not in ("negative_comparator",):
            raise RuntimeError(f"{label} failed with exit {result['returncode']}")
        return result

    try:
        if head != args.expected_head or (os.environ.get("GITHUB_SHA") and head != os.environ["GITHUB_SHA"]):
            raise ValueError("hosted checkout is not the requested exact head")
        receipt["toolchains"]["source"] = (root / "lean-toolchain").read_text().strip()
        receipt["source"] = source_contract(root)
        stage("contract", [sys.executable, f"{FAMILY}/check_contract.py",
                           "--source-root", ".", "--self-test"])
        if args.contract_only:
            receipt["passed"] = True
            return 0

        receipt["toolchains"]["comparator"] = (
            args.comparator_bin.resolve().parents[3] / "lean-toolchain").read_text().strip()

        # A cached Challenge is never trusted; the one compared below is rebuilt here.
        for build_root in (root / ".lake/build/lib/lean", root / ".lake/build/ir"):
            challenge_outputs = build_root / FAMILY
            if challenge_outputs.is_dir():
                import shutil
                shutil.rmtree(challenge_outputs)
        stage("challenge", ["lake", "build", f"{FAMILY}.Challenge"], lean=True)
        stage("solution", ["lake", "build", f"{FAMILY}.Solution"], lean=True)
        stage("negative_solution", ["lake", "build", f"{FAMILY}.NegativeSolution"], lean=True)
        audit = stage("axiom_audit", ["lake", "env", "lean", f"{FAMILY}/AxiomAudit.lean"], lean=True)
        receipt["axioms"] = audit_axioms(audit["log"] or "")

        sandbox = sandbox_preflight(runner, out)
        receipt["sandbox_mode"] = sandbox
        if sandbox == "unavailable":
            raise RuntimeError("supported systemd sandbox unavailable")
        common = dict(
            sandbox_mode=sandbox, comparator_bin=str(args.comparator_bin.resolve()),
            working_directory=str(root), path=os.environ.get("PATH", ""),
            landrun=str(args.landrun.resolve()), nanoda=str(args.nanoda.resolve()),
            lean4export=str(args.lean4export.resolve()),
            user=subprocess.check_output(["id", "-un"], text=True).strip(),
            group=subprocess.check_output(["id", "-gn"], text=True).strip(),
            timeout="180m",
        )
        positive_argv = comparator_argv(config=f"{FAMILY}/comparator.json", **common)
        positive = stage("positive_comparator", positive_argv)
        receipt["positive"] = classify_comparator(positive["returncode"], positive["log"] or "")
        if receipt["positive"]["exit"] != 0:
            raise RuntimeError("positive Comparator or independent kernel acceptance failed")

        negative_argv = comparator_argv(config=f"{FAMILY}/comparator-negative-mismatch.json", **common)
        negative = stage("negative_comparator", negative_argv)
        negative_text = negative["log"] or ""
        receipt["negative"] = {
            **classify_comparator(negative["returncode"], negative_text),
            "expected_mismatch_diagnostic": MISMATCH in negative_text,
        }
        if (negative["returncode"] == 0 or MISMATCH not in negative_text
                or receipt["negative"]["nanoda_acceptance"]
                or receipt["negative"]["lean_acceptance"]):
            raise RuntimeError("deliberate statement mismatch did not fail as expected")
        receipt["passed"] = True
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        receipt["failure"] = f"{type(error).__name__}: {error}"
        return 1
    finally:
        receipt["raw_log_sha256"] = {path.name: sha(path) for path in sorted(out.glob("*.log"))}
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"head": head, "passed": receipt["passed"],
                          "failure": receipt["failure"], "receipt": str(out / "receipt.json")}),
              flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--comparator-bin", type=Path)
    parser.add_argument("--landrun", type=Path)
    parser.add_argument("--lean4export", type=Path)
    parser.add_argument("--nanoda", type=Path)
    parser.add_argument("--contract-only", action="store_true")
    args = parser.parse_args()
    if not args.contract_only and not all((args.comparator_bin, args.landrun,
                                           args.lean4export, args.nanoda)):
        parser.error("Comparator, landrun, lean4export, and NanoDa paths are required")
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
