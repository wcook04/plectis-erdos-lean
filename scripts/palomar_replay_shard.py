#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The Comparator replay's entry verification unit, and the runner scheduling unit.

These are two different things and this module keeps them apart on purpose.

**The entry verification unit** is one publication entry: build its Challenge, build its
Solution, run the pinned Comparator on it, replay Palomar's core-notation audit, and write
one self-contained result file, `receipt-<entry>.json`. `verify_entry` is the only code
path that does this, and `run_shard` calls it in a loop. Nothing in the result depends on
which other entries happened to share the runner: no shard id, no neighbour's exit code, no
`$GITHUB_OUTPUT` key that a later entry can overwrite. That independence is the property
`scripts/test_palomar_replay_shard.py` asserts byte for byte, because it is the only reason
a shard may be trusted to say the same thing about an entry that a single-entry job said.

**The runner scheduling unit** is a shard: a group of entries that share one GitHub job so
the fixed setup cost (runner boot, checkout, elan, the Mathlib cache restore, and the pinned
Comparator / lean4export / landrun / NanoDa build — a median 2.6 min per job, measured over
the 144 replay jobs of run 35643815458) is paid once instead of once per entry. `plan_shards`
composes shards from measured per-entry durations. Sharding is a cost decision and it is
recorded only in `shard-manifest.json`, never in an entry's result.

The manifest keeps two questions apart, because collapsing them is how a dropped entry hides:

* `complete` — did every entry this shard promised produce a result file?
* `all_passed` — did every entry this shard promised compare green?

A shard is red if either is false, and the reconciliation in
`tools/meta/formal_math/comparator_identity_receipts.py` classifies every expected entry from
the corpus commit, so a green shard can never stand in for its promised entries.

No part of this module submits, registers, or claims a Palomar verdict.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence

PLAN_SCHEMA = "palomar_replay_shard_plan_v1"
MANIFEST_SCHEMA = "palomar_replay_shard_manifest_v1"
DURATIONS_SCHEMA = "palomar_replay_entry_durations_v1"
#: Unchanged on purpose. The harvester selects receipt files by this exact string, so a
#: bumped schema would make every delivered receipt invisible to it. New fields are
#: additive and no existing field changes meaning.
RECEIPT_SCHEMA = "palomar_replay_receipt_v1"

PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
ENTRY_RE = re.compile(r"^E(?:" + "|".join(str(n) for n in PROBLEMS) + r")[a-z]{0,2}$")

#: GitHub refuses a matrix larger than this, and it fails the run without naming the cause.
MATRIX_CAP = 256
#: Target wall time for one shard. Chosen against the measured p90 entry cost so a typical
#: shard finishes well inside the job's `timeout-minutes`.
DEFAULT_TARGET_SECONDS = 1800
#: Shard budget. 60 shards for 208 entries leaves the matrix room to grow to roughly four
#: times the current corpus before the cap is anywhere near.
DEFAULT_MAX_SHARDS = 60
#: An entry at or above this cost gets a shard of its own, so one 20-minute entry cannot
#: drag a shard of ordinary entries past the timeout.
DEFAULT_HEAVY_SECONDS = 900
#: What an entry with no measurement is assumed to cost.
DEFAULT_ENTRY_SECONDS = 300

ENTRY_DIGEST_FILES = ("Challenge.lean", "comparator.json", "formalization.yaml")

STAGE_CHALLENGE = "build_challenge"
STAGE_SOLUTION = "build_solution"
STAGE_COMPARATOR = "run_comparator"
STAGE_RENDER_AUDIT = "render_audit"

NOT_ESTABLISHED = [
    "Palomar mechanical verification",
    "Palomar editorial review",
    "Palomar registration",
]


# --------------------------------------------------------------------- scheduling unit


def discover_entries(corpus_root: Path) -> list[str]:
    """Every publication entry in the tree, by the same rule the workflow's inventory uses."""
    found = sorted(
        path.parent.name
        for path in Path(corpus_root, "PalomarCorpus").glob("E*/comparator.json")
    )
    stray = [name for name in found if not ENTRY_RE.match(name)]
    if stray:
        raise SystemExit(f"unrecognised PalomarCorpus entries: {stray}")
    return found


def load_durations(path: Path | None) -> dict[str, Any]:
    """The measured per-entry cost sidecar, or an empty heuristic when it is absent.

    An absent, unreadable or wrong-schema sidecar is not an error: the planner then falls
    back to equal-size shards. A scheduling heuristic must never be able to fail a run.
    """
    empty = {"entry_seconds": {}, "default_seconds": DEFAULT_ENTRY_SECONDS,
             "source_runs": [], "fixed_overhead_seconds": None, "path": None}
    if path is None or not Path(path).is_file():
        return empty
    try:
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return empty
    if payload.get("schema") != DURATIONS_SCHEMA:
        return empty
    seconds = {
        str(entry): float(value)
        for entry, value in (payload.get("entry_seconds") or {}).items()
        if isinstance(value, (int, float)) and value > 0
    }
    return {
        "entry_seconds": seconds,
        "default_seconds": float(payload.get("default_seconds") or DEFAULT_ENTRY_SECONDS),
        "source_runs": list(payload.get("source_runs") or []),
        "fixed_overhead_seconds": payload.get("fixed_overhead_seconds"),
        "path": str(path),
    }


def _pack(entries: Sequence[str], cost: dict[str, float], capacity: float) -> list[list[str]]:
    """First-fit-decreasing bin packing. Deterministic for a fixed input."""
    bins: list[list[str]] = []
    loads: list[float] = []
    for entry in sorted(entries, key=lambda name: (-cost[name], name)):
        for index, load in enumerate(loads):
            if load + cost[entry] <= capacity:
                bins[index].append(entry)
                loads[index] += cost[entry]
                break
        else:
            bins.append([entry])
            loads.append(cost[entry])
    return bins


def plan_shards(
    entries: Iterable[str],
    *,
    entry_seconds: dict[str, float] | None = None,
    default_seconds: float = DEFAULT_ENTRY_SECONDS,
    target_seconds: float = DEFAULT_TARGET_SECONDS,
    max_shards: int = DEFAULT_MAX_SHARDS,
    heavy_seconds: float = DEFAULT_HEAVY_SECONDS,
) -> list[dict[str, Any]]:
    """Compose shards from the entry population, isolating the unusually heavy entries.

    Pure and deterministic: the same entries and the same sidecar always give the same plan,
    which is what lets the reconciliation recompute a mapping it did not observe.

    An entry costing at least ``heavy_seconds`` gets a shard of its own. The rest are packed
    first-fit-decreasing into shards of ``target_seconds``. If that would need more than
    ``max_shards`` jobs the capacity is raised until it fits, so the shard budget is a
    guarantee and not an aspiration. Isolation is itself budgeted, so a corpus of nothing but
    heavy entries cannot blow the matrix either.
    """
    names = sorted(set(str(entry) for entry in entries))
    if not names:
        return []
    if max_shards < 1:
        raise ValueError("max_shards must be at least 1")
    seconds = entry_seconds or {}
    cost = {name: float(seconds.get(name, default_seconds)) for name in names}

    isolate_budget = max(1, max_shards // 3)
    heavy = [
        name for name in sorted(names, key=lambda item: (-cost[item], item))
        if cost[name] >= heavy_seconds
    ][:isolate_budget]
    heavy_set = set(heavy)
    light = [name for name in names if name not in heavy_set]

    capacity = float(target_seconds)
    bins: list[list[str]] = []
    for _ in range(128):
        bins = _pack(light, cost, capacity)
        if len(heavy) + len(bins) <= max_shards:
            break
        capacity = math.ceil(capacity * 1.25)
    else:  # pragma: no cover - the capacity growth above always converges
        bins = [light] if light else []
    groups = [[name] for name in sorted(heavy)] + bins
    if len(groups) > MATRIX_CAP:
        raise SystemExit(
            f"{len(groups)} shards exceeds the {MATRIX_CAP}-job matrix cap for {len(names)} entries"
        )

    # Heaviest shard first so the long pole starts while runners are free; the ids are
    # assigned after that ordering so a shard id names a stable position in the plan.
    ordered = sorted(groups, key=lambda group: (-sum(cost[name] for name in group), group[0]))
    width = max(2, len(str(len(ordered))))
    plan: list[dict[str, Any]] = []
    for index, group in enumerate(ordered, start=1):
        members = sorted(group)
        plan.append({
            "shard_id": f"shard-{index:0{width}d}",
            "entries": members,
            "entry_count": len(members),
            "estimated_seconds": int(round(sum(cost[name] for name in members))),
            "measured_entries": sum(1 for name in members if name in seconds),
            "isolated": len(members) == 1 and members[0] in heavy_set,
        })
    return plan


def build_plan(
    corpus_root: Path,
    *,
    durations_path: Path | None,
    target_seconds: float = DEFAULT_TARGET_SECONDS,
    max_shards: int = DEFAULT_MAX_SHARDS,
    heavy_seconds: float = DEFAULT_HEAVY_SECONDS,
    entries: Sequence[str] | None = None,
    commit: str | None = None,
    now: Callable[[], str] | None = None,
) -> dict[str, Any]:
    """The full shard plan payload, including the estimate that justifies it."""
    population = list(entries) if entries is not None else discover_entries(corpus_root)
    if len(population) > MATRIX_CAP:
        raise SystemExit(
            f"{len(population)} entries exceeds the {MATRIX_CAP}-job matrix cap even before "
            "sharding; the cap assertion in the discover job is the backstop for this"
        )
    durations = load_durations(durations_path)
    shards = plan_shards(
        population,
        entry_seconds=durations["entry_seconds"],
        default_seconds=durations["default_seconds"],
        target_seconds=target_seconds,
        max_shards=max_shards,
        heavy_seconds=heavy_seconds,
    )
    estimates = sorted(shard["estimated_seconds"] for shard in shards)
    overhead = durations["fixed_overhead_seconds"]
    return {
        "schema": PLAN_SCHEMA,
        "generated_at": (now or _utc_now)(),
        "commit": commit or os.environ.get("GITHUB_SHA"),
        "entry_count": len(population),
        "shard_count": len(shards),
        "entries": population,
        "shards": shards,
        "isolated_entries": [
            shard["entries"][0] for shard in shards if shard.get("isolated")
        ],
        "unmeasured_entries": sorted(
            name for name in population if name not in durations["entry_seconds"]
        ),
        "planner": {
            "target_seconds": int(target_seconds),
            "max_shards": int(max_shards),
            "heavy_seconds": int(heavy_seconds),
            "default_seconds": int(durations["default_seconds"]),
            "matrix_cap": MATRIX_CAP,
            "durations_path": durations["path"],
            "durations_source_runs": durations["source_runs"],
            "fixed_overhead_seconds": overhead,
        },
        "estimate": {
            "total_entry_seconds": sum(estimates),
            "min_shard_seconds": estimates[0] if estimates else 0,
            "median_shard_seconds": estimates[len(estimates) // 2] if estimates else 0,
            "max_shard_seconds": estimates[-1] if estimates else 0,
            "fixed_overhead_paid_per_entry_seconds": (
                int(overhead) * len(population) if isinstance(overhead, (int, float)) else None
            ),
            "fixed_overhead_paid_per_shard_seconds": (
                int(overhead) * len(shards) if isinstance(overhead, (int, float)) else None
            ),
        },
        "boundary": (
            "A scheduling plan. It decides which runner job carries which entry and "
            "nothing else: it never enters an entry's result file and it establishes no "
            "Comparator or Palomar status."
        ),
    }


def shard_map(plan: dict[str, Any]) -> dict[str, list[str]]:
    """shard id -> the entries that shard promised."""
    return {str(shard["shard_id"]): list(shard["entries"]) for shard in plan.get("shards") or []}


def shard_entries(plan: dict[str, Any], shard_id: str) -> list[str]:
    mapping = shard_map(plan)
    if shard_id not in mapping:
        raise SystemExit(f"shard {shard_id} is not in this plan ({sorted(mapping)[:6]}...)")
    return mapping[shard_id]


# ---------------------------------------------------------------- verification unit


def _utc_now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sha256_file(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def solution_digest(corpus_root: Path, entry: str) -> dict[str, Any]:
    """The Solution side of the comparison, digested.

    The receipt has always carried the Challenge and comparator.json digests and never the
    Solution's, so a reader could not tell which Solution bytes were compared. This is a new
    field beside them, never inside `entry_digests`: the reconciliation resolves every name
    in `entry_digests` against `PalomarCorpus/<entry>/`, and a Solution path is not there.
    """
    module = Path("Solutions/PalomarCorpus")
    candidates: list[Path] = []
    single = corpus_root / module / f"{entry}.lean"
    if single.is_file():
        candidates.append(single)
    directory = corpus_root / module / entry
    if directory.is_dir():
        candidates.extend(sorted(path for path in directory.rglob("*.lean") if path.is_file()))
    files = {
        path.relative_to(corpus_root).as_posix(): sha256_file(path) for path in candidates
    }
    rollup = hashlib.sha256()
    for relpath in sorted(files):
        rollup.update(relpath.encode("utf-8"))
        rollup.update(b"\0")
        rollup.update((files[relpath] or "").encode("utf-8"))
        rollup.update(b"\n")
    return {"files": files, "sha256": rollup.hexdigest() if files else None}


def comparator_argv(
    *,
    sandbox_mode: str,
    config: str,
    comparator_bin: str,
    working_directory: str,
    path: str,
    landrun: str,
    nanoda: str,
    lean4export: str,
    user: str | None = None,
    group: str | None = None,
    timeout: str = "45m",
) -> list[str] | None:
    """The exact command the replay runs, or None when no sandbox manager is usable.

    Pure, so the two sandbox shapes are testable without systemd. The argv is the shell
    command the single-entry workflow ran, transcribed: same timeout, same
    `RestrictAddressFamilies`, same four environment exports, same `lake env comparator`.
    """
    exports = [
        "-E", f"PATH={path}",
        "-E", f"COMPARATOR_LANDRUN={landrun}",
        "-E", f"COMPARATOR_NANODA={nanoda}",
        "-E", f"COMPARATOR_LEAN4EXPORT={lean4export}",
    ]
    tail = [f"--working-directory={working_directory}", "--", "lake", "env", comparator_bin, config]
    if sandbox_mode == "user-manager":
        return ["timeout", timeout, "systemd-run",
                "--property=RestrictAddressFamilies=~AF_UNIX", "--user", "--pipe",
                *exports, *tail]
    if sandbox_mode == "system-manager-nonprivileged-unit":
        return ["timeout", timeout, "sudo", "-n", "systemd-run",
                "--property=RestrictAddressFamilies=~AF_UNIX",
                f"--uid={user}", f"--gid={group}", "--pipe",
                *exports, *tail]
    return None


def render_audit_argv(
    *, audit_script: str, module: str, theorem_names: Sequence[str], timeout: str = "20m"
) -> list[str]:
    argv = ["timeout", timeout, "lake", "env", "lean", "--run", audit_script, module]
    for name in theorem_names:
        argv.extend(["theorem", name])
    return argv


def classify_comparator(process_exit: int, log_text: str) -> dict[str, Any]:
    """The replay's verdict rule, unchanged from the single-entry workflow.

    A green process exit must carry both independent kernel acceptance lines, because
    Palomar's protected configuration forces NanoDa and a run that skipped a kernel is not
    green. 90 is a missing NanoDa line, 91 a missing Lean line; the raw process exit is kept
    beside the verdict as diagnostic evidence.
    """
    lines = log_text.splitlines()
    nanoda = any(line.startswith("nanoda kernel accepts the solution") for line in lines)
    lean = any(line.startswith("Lean default kernel accepts the solution") for line in lines)
    verdict = process_exit
    if verdict == 0 and not nanoda:
        verdict = 90
    if verdict == 0 and not lean:
        verdict = 91
    return {
        "exit": verdict,
        "process_exit": process_exit,
        "nanoda_acceptance": nanoda,
        "lean_acceptance": lean,
    }


class SubprocessRunner:
    """Runs one verification stage for real, capturing its output to a log file.

    The runner is injected so `verify_entry` can be exercised without Lean, a network, or a
    sandbox. It returns the stage's exit code and wall seconds and nothing else: a runner
    cannot influence the verdict rule, only report what the command did.
    """

    def __init__(self, *, cwd: Path, env: dict[str, str] | None = None) -> None:
        self.cwd = Path(cwd)
        self.env = env

    def __call__(
        self, stage: str, argv: Sequence[str] | None, *, log_path: Path | None = None,
        env: dict[str, str] | None = None,
    ) -> dict[str, Any]:
        if argv is None:
            return {"returncode": 125, "seconds": 0.0, "log": None}
        environ = {**os.environ, **(self.env or {}), **(env or {})}
        started = time.monotonic()
        result = subprocess.run(
            list(argv), cwd=self.cwd, env=environ, capture_output=True, text=True, check=False
        )
        elapsed = time.monotonic() - started
        output = (result.stdout or "") + (result.stderr or "")
        if log_path is not None:
            Path(log_path).parent.mkdir(parents=True, exist_ok=True)
            Path(log_path).write_text(output, encoding="utf-8")
        return {"returncode": result.returncode, "seconds": round(elapsed, 3),
                "log": output, "stage": stage}


def sandbox_preflight(runner: Any, out_dir: Path) -> str:
    """Which systemd transient-unit manager this runner can use, decided once per shard.

    Shard-level by nature: it is a property of the machine, not of an entry. It is recorded
    in each entry's result because the entry was compared under it, and the preflight logs
    go beside the manifest.
    """
    user = runner("sandbox_preflight_user", ["systemctl", "--user", "show-environment"],
                  log_path=out_dir / "systemd-user-preflight.log")
    if user["returncode"] == 0:
        return "user-manager"
    system = runner("sandbox_preflight_system", ["sudo", "-n", "systemctl", "show-environment"],
                    log_path=out_dir / "systemd-system-preflight.log")
    if system["returncode"] == 0:
        return "system-manager-nonprivileged-unit"
    return "unavailable"


def verify_entry(
    entry: str,
    *,
    corpus_root: Path,
    out_dir: Path,
    runner: Any,
    context: dict[str, Any],
    now: Callable[[], str] | None = None,
) -> dict[str, Any]:
    """Verify one entry and write its self-contained result file.

    The returned record and the file it writes depend on this entry, the corpus tree, the
    pinned tool revisions and the runner's answers. They do not depend on any other entry,
    on how many entries share this runner, or on any mutable step output. A single-entry
    shard and an N-entry shard therefore write byte-identical result files for the same
    inputs, which `scripts/test_palomar_replay_shard.py` asserts.
    """
    clock = now or _utc_now
    corpus_root = Path(corpus_root)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    entry_dir = corpus_root / "PalomarCorpus" / entry
    result_file = out_dir / f"receipt-{entry}.json"
    stages: list[dict[str, Any]] = []

    def record(stage: str, outcome: dict[str, Any]) -> int:
        stages.append({
            "stage": stage,
            "returncode": outcome.get("returncode"),
            "seconds": outcome.get("seconds"),
        })
        return int(outcome.get("returncode") or 0)

    try:
        config = json.loads((entry_dir / "comparator.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        receipt = _receipt(
            entry=entry, config={}, corpus_root=corpus_root, entry_dir=entry_dir,
            context=context, generated_at=clock(), stages=stages,
            comparison={"exit": None, "process_exit": None,
                        "nanoda_acceptance": False, "lean_acceptance": False},
            render_audit_exit=None, failure_stage="read_comparator_config",
            error=f"{type(error).__name__}: {error}",
        )
        _write_json(result_file, receipt)
        return {"entry": entry, "receipt": receipt, "result_file": result_file.name,
                "exit": None, "passed": False, "seconds": 0.0,
                "failure_stage": "read_comparator_config"}

    theorem_names = list(config.get("theorem_names") or [])
    failure_stage: str | None = None

    challenge_rc = record(STAGE_CHALLENGE, runner(
        STAGE_CHALLENGE, ["lake", "build", f"PalomarCorpus.{entry}.Challenge"],
        log_path=out_dir / f"build-challenge-{entry}.log",
        env={"LEAN_NUM_THREADS": "2"},
    ))
    solution_rc = 0
    if challenge_rc == 0:
        solution_rc = record(STAGE_SOLUTION, runner(
            STAGE_SOLUTION, ["lake", "build", f"Solutions.PalomarCorpus.{entry}"],
            log_path=out_dir / f"build-solution-{entry}.log",
            env={"LEAN_NUM_THREADS": "2"},
        ))
    else:
        failure_stage = STAGE_CHALLENGE
    if failure_stage is None and solution_rc != 0:
        failure_stage = STAGE_SOLUTION

    if failure_stage is None:
        argv = comparator_argv(
            sandbox_mode=str(context.get("sandbox_mode")),
            config=f"PalomarCorpus/{entry}/comparator.json",
            comparator_bin=str(context.get("comparator_bin")),
            working_directory=str(context.get("working_directory") or corpus_root),
            path=str(context.get("path") or ""),
            landrun=str(context.get("landrun") or ""),
            nanoda=str(context.get("nanoda") or ""),
            lean4export=str(context.get("lean4export") or ""),
            user=context.get("user"),
            group=context.get("group"),
        )
        log_path = out_dir / f"{entry}.log"
        outcome = runner(STAGE_COMPARATOR, argv, log_path=log_path)
        if argv is None:
            _write_text(log_path, "No usable systemd transient-unit manager; "
                                  "refusing an insecure fallback.\n")
        process_rc = record(STAGE_COMPARATOR, outcome)
        log_text = outcome.get("log")
        if log_text is None:
            log_text = log_path.read_text(encoding="utf-8", errors="replace") \
                if log_path.is_file() else ""
        comparison = classify_comparator(process_rc, log_text)
    else:
        # The Comparator never ran, so it has no verdict to report. A null exit is what the
        # single-entry workflow's `if: always()` receipt recorded when a build step failed
        # ahead of it, and the reconciliation reads a null exit as a comparison failure.
        comparison = {"exit": None, "process_exit": None,
                      "nanoda_acceptance": False, "lean_acceptance": False}

    render_audit_exit: int | None = None
    audit_script = context.get("audit_script")
    if not audit_script:
        render_audit_exit = None
    elif failure_stage is not None:
        render_audit_exit = None
    else:
        outcome = runner(STAGE_RENDER_AUDIT, render_audit_argv(
            audit_script=str(audit_script),
            module=str(config.get("challenge_module")),
            theorem_names=theorem_names,
        ), log_path=out_dir / f"render-audit-{entry}.log")
        render_audit_exit = record(STAGE_RENDER_AUDIT, outcome)

    receipt = _receipt(
        entry=entry, config=config, corpus_root=corpus_root, entry_dir=entry_dir,
        context=context, generated_at=clock(), stages=stages, comparison=comparison,
        render_audit_exit=render_audit_exit, failure_stage=failure_stage, error=None,
    )
    _write_json(result_file, receipt)
    return {
        "entry": entry,
        "receipt": receipt,
        "result_file": result_file.name,
        "exit": comparison["exit"],
        "passed": comparison["exit"] == 0 and comparison["process_exit"] == 0,
        "seconds": round(sum(float(row["seconds"] or 0) for row in stages), 3),
        "failure_stage": failure_stage,
    }


def _receipt(
    *,
    entry: str,
    config: dict[str, Any],
    corpus_root: Path,
    entry_dir: Path,
    context: dict[str, Any],
    generated_at: str,
    stages: list[dict[str, Any]],
    comparison: dict[str, Any],
    render_audit_exit: int | None,
    failure_stage: str | None,
    error: str | None,
) -> dict[str, Any]:
    """The per-entry result file.

    `palomar_replay_receipt_v1` with additive fields. Every field the single-entry workflow
    wrote is present with the same name, type and meaning, because the reconciliation and
    the harvester read them: `entry`, `github`, `lean_toolchain`, `comparator_lean_toolchain`,
    `tool_revisions`, `challenge_module`, `solution_module`, `theorem_count`,
    `theorem_names`, `permitted_axioms`, `entry_digests`, `sandbox_mode`, `exit`,
    `process_exit`, `kernel_acceptance`, `render_audit_exit`, `not_established`. The digests
    are recomputed from the tree here, so a result can never describe a different tree from
    the one that was verified. New: `verification`, `stages`, `axiom_audit`, `solution`.
    """
    github = context.get("github") or {}
    return {
        "schema": RECEIPT_SCHEMA,
        "generated_at": generated_at,
        "entry": entry,
        "github": {
            "sha": github.get("sha"),
            "ref": github.get("ref"),
            "repository": github.get("repository"),
            "run_id": github.get("run_id"),
            "run_attempt": github.get("run_attempt"),
            "workflow": github.get("workflow"),
        },
        "lean_toolchain": context.get("lean_toolchain"),
        "comparator_lean_toolchain": context.get("comparator_lean_toolchain") or None,
        "tool_revisions": dict(context.get("tool_revisions") or {}),
        "challenge_module": config.get("challenge_module"),
        "solution_module": config.get("solution_module"),
        "theorem_count": len(config.get("theorem_names") or []),
        "theorem_names": config.get("theorem_names") or [],
        "permitted_axioms": config.get("permitted_axioms") or [],
        "entry_digests": {name: sha256_file(entry_dir / name) for name in ENTRY_DIGEST_FILES},
        "solution": solution_digest(corpus_root, entry),
        "sandbox_mode": context.get("sandbox_mode"),
        "exit": comparison["exit"],
        "process_exit": comparison["process_exit"],
        "kernel_acceptance": {
            "lean_default": bool(comparison["lean_acceptance"]),
            "nanoda": bool(comparison["nanoda_acceptance"]),
        },
        "render_audit_exit": render_audit_exit,
        "verification": {
            # The one-line answer for this entry, independent of any other entry and of the
            # shard that carried it. `failure_stage` names where it stopped, so a null exit
            # is never ambiguous between "the Comparator said nothing" and "it was never run".
            "outcome": "passed" if comparison["exit"] == 0 and comparison["process_exit"] == 0
                       else "failed",
            "failure_stage": failure_stage,
            "error": error,
        },
        "stages": stages,
        "axiom_audit": {
            # What this replay actually enforces about axioms: the Comparator checks the
            # Solution environment against the entry's own `permitted_axioms`, and the render
            # audit replays Palomar's core-notation pass. No separate axiom scan runs per
            # entry, and saying so is the point of the null below.
            "permitted_axioms": config.get("permitted_axioms") or [],
            "enforced_by": "comparator" if comparison["exit"] == 0 else None,
            "render_audit_exit": render_audit_exit,
            "independent_axiom_scan": None,
        },
        "not_established": list(NOT_ESTABLISHED),
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(text, encoding="utf-8")


def run_shard(
    shard_id: str,
    entries: Sequence[str],
    *,
    corpus_root: Path,
    out_dir: Path,
    runner: Any,
    context: dict[str, Any],
    now: Callable[[], str] | None = None,
) -> dict[str, Any]:
    """Verify every entry this shard promised, sequentially, and write the shard manifest.

    One entry's failure never stops the others: `verify_entry` is called inside a `try` and
    an entry that raises still gets a result file recording the error, so a promised entry is
    never silently absent. The manifest then keeps `complete` (every promised entry produced
    a result file) apart from `all_passed` (every promised entry compared green), because
    folding those together is exactly how a dropped entry would hide behind a green shard.
    """
    clock = now or _utc_now
    promised = list(entries)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    status: dict[str, Any] = {}
    for entry in promised:
        try:
            record = verify_entry(entry, corpus_root=corpus_root, out_dir=out_dir,
                                  runner=runner, context=context, now=clock)
        except Exception as error:  # noqa: BLE001 - one entry must not fell the shard
            receipt = _receipt(
                entry=entry, config={}, corpus_root=Path(corpus_root),
                entry_dir=Path(corpus_root) / "PalomarCorpus" / entry, context=context,
                generated_at=clock(), stages=[],
                comparison={"exit": None, "process_exit": None,
                            "nanoda_acceptance": False, "lean_acceptance": False},
                render_audit_exit=None, failure_stage="verify_entry_raised",
                error=f"{type(error).__name__}: {error}",
            )
            _write_json(out_dir / f"receipt-{entry}.json", receipt)
            record = {"entry": entry, "result_file": f"receipt-{entry}.json", "exit": None,
                      "passed": False, "seconds": 0.0, "failure_stage": "verify_entry_raised"}
        status[entry] = {
            "result_file": record["result_file"],
            "exit": record["exit"],
            "passed": bool(record["passed"]),
            "failure_stage": record.get("failure_stage"),
            "seconds": record.get("seconds"),
        }
        print(f"{shard_id} {entry} exit={record['exit']} "
              f"passed={record['passed']} stage={record.get('failure_stage')}", flush=True)

    delivered = [entry for entry in promised if (out_dir / f"receipt-{entry}.json").is_file()]
    missing = [entry for entry in promised if entry not in delivered]
    failed = sorted(entry for entry, row in status.items() if not row["passed"])
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "generated_at": clock(),
        "shard_id": shard_id,
        "github": dict(context.get("github") or {}),
        "sandbox_mode": context.get("sandbox_mode"),
        "promised_entries": promised,
        "delivered_entries": delivered,
        "missing_entries": missing,
        "failed_entries": failed,
        "entry_status": status,
        # Two separate questions, deliberately not one flag.
        "complete": not missing,
        "all_passed": not failed and not missing,
        "observed_seconds": round(time.monotonic() - started, 3),
        "boundary": (
            "Scheduling bookkeeping for one runner job. It records which entries this job "
            "promised and whether each produced a result; the verdict for an entry lives in "
            "that entry's own result file and nowhere else."
        ),
    }
    _write_json(out_dir / "shard-manifest.json", manifest)
    return manifest


# ------------------------------------------------------------------------ run coverage


def check_run_coverage(
    plan: dict[str, Any], receipts_dir: Path, *, expected_entries: Sequence[str] | None = None
) -> dict[str, Any]:
    """Every entry the plan promised has a delivered, green result file. No shard stands in.

    This is the in-CI form of the reconciliation's completeness invariant: it starts from the
    entry population and asks what arrived, never from the artifacts and what they contain.
    """
    promised = sorted({entry for entries in shard_map(plan).values() for entry in entries})
    plan_entries = sorted(plan.get("entries") or [])
    problems: list[str] = []
    if promised != plan_entries:
        problems.append(
            "the plan's shards do not cover its entry population: "
            f"{sorted(set(plan_entries) - set(promised))} unpromised, "
            f"{sorted(set(promised) - set(plan_entries))} unexpected"
        )
    if expected_entries is not None:
        expected = sorted(set(str(entry) for entry in expected_entries))
        if expected != plan_entries:
            problems.append(
                "the plan was built for a different entry population than the run discovered: "
                f"{sorted(set(expected) - set(plan_entries))} missing from the plan, "
                f"{sorted(set(plan_entries) - set(expected))} not discovered"
            )

    delivered: dict[str, list[Path]] = {}
    for path in sorted(Path(receipts_dir).rglob("receipt-*.json")):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            problems.append(f"{path.name} is not readable JSON")
            continue
        if payload.get("schema") != RECEIPT_SCHEMA or not isinstance(payload.get("entry"), str):
            continue
        delivered.setdefault(payload["entry"], []).append(path)

    missing, red = [], []
    for entry in promised:
        files = delivered.get(entry)
        if not files:
            missing.append(entry)
            continue
        payload = json.loads(files[-1].read_text(encoding="utf-8"))
        kernels = payload.get("kernel_acceptance") or {}
        if (payload.get("exit") != 0 or payload.get("process_exit") != 0
                or kernels.get("lean_default") is not True or kernels.get("nanoda") is not True):
            red.append(entry)
    if missing:
        problems.append(f"{len(missing)} promised entries delivered no result file: {missing}")
    if red:
        problems.append(f"{len(red)} promised entries did not compare green: {red}")
    return {
        "promised": len(promised),
        "delivered": len(delivered),
        "missing_entries": missing,
        "red_entries": red,
        "unexpected_entries": sorted(set(delivered) - set(promised)),
        "problems": problems,
        "ok": not problems,
    }


# -------------------------------------------------------------------------------- CLI


def _github_context() -> dict[str, Any]:
    return {key: os.environ.get(f"GITHUB_{key.upper()}")
            for key in ("sha", "ref", "repository", "run_id", "run_attempt", "workflow")}


def _emit_output(pairs: dict[str, str]) -> None:
    target = os.environ.get("GITHUB_OUTPUT")
    if not target:
        return
    with open(target, "a", encoding="utf-8") as handle:
        for key, value in pairs.items():
            handle.write(f"{key}={value}\n")


def _cmd_plan(args: argparse.Namespace) -> int:
    plan = build_plan(
        args.corpus_root,
        durations_path=args.durations,
        target_seconds=args.target_seconds,
        max_shards=args.max_shards,
        heavy_seconds=args.heavy_seconds,
        commit=args.commit,
    )
    _write_json(args.out, plan)
    for shard in plan["shards"]:
        print(f"{shard['shard_id']}: {shard['entry_count']} entries, "
              f"~{shard['estimated_seconds']}s"
              f"{' (isolated)' if shard['isolated'] else ''}  {' '.join(shard['entries'])}")
    estimate = plan["estimate"]
    print(f"\n{plan['entry_count']} entries -> {plan['shard_count']} shards "
          f"(cap {MATRIX_CAP}, budget {plan['planner']['max_shards']}); "
          f"shard seconds min {estimate['min_shard_seconds']} "
          f"median {estimate['median_shard_seconds']} max {estimate['max_shard_seconds']}; "
          f"{len(plan['isolated_entries'])} isolated, "
          f"{len(plan['unmeasured_entries'])} unmeasured")
    if plan["shard_count"] > MATRIX_CAP:
        raise SystemExit(f"{plan['shard_count']} shards exceeds the {MATRIX_CAP}-job matrix cap")
    _emit_output({
        "shards": json.dumps([shard["shard_id"] for shard in plan["shards"]]),
        "shard_count": str(plan["shard_count"]),
        "entry_count": str(plan["entry_count"]),
    })
    return 0


def _cmd_run_shard(args: argparse.Namespace) -> int:
    plan = json.loads(Path(args.plan).read_text(encoding="utf-8"))
    if plan.get("schema") != PLAN_SCHEMA:
        raise SystemExit(f"{args.plan} is not a {PLAN_SCHEMA}")
    entries = shard_entries(plan, args.shard_id)
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    runner = SubprocessRunner(cwd=args.corpus_root)
    sandbox = args.sandbox_mode or sandbox_preflight(runner, out_dir)
    comparator_toolchain = None
    if args.comparator_toolchain_file and Path(args.comparator_toolchain_file).is_file():
        comparator_toolchain = Path(args.comparator_toolchain_file).read_text(
            encoding="utf-8").strip()
    lean_toolchain = (Path(args.corpus_root) / "lean-toolchain").read_text(
        encoding="utf-8").strip()
    context = {
        "github": _github_context(),
        "lean_toolchain": lean_toolchain,
        "comparator_lean_toolchain": comparator_toolchain,
        "tool_revisions": {
            "comparator": os.environ.get("COMPARATOR_REV"),
            "lean4export": os.environ.get("LEAN4EXPORT_REV"),
            "landrun": os.environ.get("LANDRUN_REV"),
            "nanoda": os.environ.get("NANODA_REV"),
            "renderer": os.environ.get("RENDERER_REV"),
        },
        "sandbox_mode": sandbox,
        "comparator_bin": args.comparator_bin,
        "landrun": args.landrun,
        "nanoda": args.nanoda,
        "lean4export": args.lean4export,
        "audit_script": args.audit_script if args.audit_script
                        and Path(args.audit_script).is_file() else None,
        "working_directory": str(Path(args.corpus_root).resolve()),
        "path": os.environ.get("PATH", ""),
        "user": args.user or _id("-un"),
        "group": args.group or _id("-gn"),
    }
    manifest = run_shard(args.shard_id, entries, corpus_root=args.corpus_root, out_dir=out_dir,
                         runner=runner, context=context)
    print(json.dumps({key: manifest[key] for key in (
        "shard_id", "sandbox_mode", "complete", "all_passed",
        "missing_entries", "failed_entries", "observed_seconds")}, indent=2))
    # Always zero. The manifest is the verdict surface and the enforcing steps read it, so a
    # transport or verdict failure is never conflated with this step crashing.
    return 0


def _id(flag: str) -> str | None:
    result = subprocess.run(["id", flag], capture_output=True, text=True, check=False)
    return result.stdout.strip() or None


def _cmd_check_shard(args: argparse.Namespace) -> int:
    manifest = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise SystemExit(f"{args.manifest} is not a {MANIFEST_SCHEMA}")
    shard = manifest["shard_id"]
    if args.require == "complete":
        if manifest["complete"]:
            print(f"{shard}: every one of {len(manifest['promised_entries'])} promised entries "
                  "produced a result file")
            return 0
        print(f"{shard}: {len(manifest['missing_entries'])} promised entries produced no result "
              f"file: {manifest['missing_entries']}")
        return 1
    if manifest["all_passed"]:
        print(f"{shard}: all {len(manifest['promised_entries'])} promised entries compared green")
        return 0
    print(f"{shard}: {len(manifest['failed_entries'])} entries did not compare green: "
          f"{manifest['failed_entries']}")
    for entry in manifest["failed_entries"]:
        row = manifest["entry_status"].get(entry) or {}
        print(f"  {entry}: exit={row.get('exit')} stage={row.get('failure_stage')}")
    return 1


def _cmd_check_run(args: argparse.Namespace) -> int:
    plan = json.loads(Path(args.plan).read_text(encoding="utf-8"))
    expected = json.loads(args.expected_entries) if args.expected_entries else None
    report = check_run_coverage(plan, args.receipts_dir, expected_entries=expected)
    print(json.dumps(report, indent=2))
    return 0 if report["ok"] else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    plan_parser = sub.add_parser("plan", help="compose shards from the entry population")
    plan_parser.add_argument("--corpus-root", type=Path, default=Path("."))
    plan_parser.add_argument("--durations", type=Path,
                             default=Path(".github/replay_entry_durations.json"))
    plan_parser.add_argument("--target-seconds", type=float, default=DEFAULT_TARGET_SECONDS)
    plan_parser.add_argument("--max-shards", type=int, default=DEFAULT_MAX_SHARDS)
    plan_parser.add_argument("--heavy-seconds", type=float, default=DEFAULT_HEAVY_SECONDS)
    plan_parser.add_argument("--commit", default=None)
    plan_parser.add_argument("--out", type=Path, default=Path("artifacts/shard-plan.json"))
    plan_parser.set_defaults(func=_cmd_plan)

    run_parser = sub.add_parser("run-shard", help="verify every entry one shard promised")
    run_parser.add_argument("--shard-id", required=True)
    run_parser.add_argument("--plan", type=Path, required=True)
    run_parser.add_argument("--corpus-root", type=Path, default=Path("."))
    run_parser.add_argument("--out", type=Path, default=Path("artifacts"))
    run_parser.add_argument("--comparator-bin", required=True)
    run_parser.add_argument("--landrun", required=True)
    run_parser.add_argument("--nanoda", required=True)
    run_parser.add_argument("--lean4export", required=True)
    run_parser.add_argument("--audit-script", default=None)
    run_parser.add_argument("--comparator-toolchain-file", default=None)
    run_parser.add_argument("--sandbox-mode", default=None)
    run_parser.add_argument("--user", default=None)
    run_parser.add_argument("--group", default=None)
    run_parser.set_defaults(func=_cmd_run_shard)

    shard_check = sub.add_parser("check-shard", help="enforce completeness or greenness")
    shard_check.add_argument("--manifest", type=Path, required=True)
    shard_check.add_argument("--require", choices=("complete", "passed"), required=True)
    shard_check.set_defaults(func=_cmd_check_shard)

    run_check = sub.add_parser("check-run", help="every planned entry delivered a green result")
    run_check.add_argument("--plan", type=Path, required=True)
    run_check.add_argument("--receipts-dir", type=Path, required=True)
    run_check.add_argument("--expected-entries", default=None,
                           help="JSON list the discover job published, cross-checked "
                                "against the plan's own population")
    run_check.set_defaults(func=_cmd_check_run)

    args = parser.parse_args(list(argv) if argv is not None else None)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
