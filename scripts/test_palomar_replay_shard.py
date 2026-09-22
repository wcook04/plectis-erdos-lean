#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The property that makes sharding safe: a shard says what single-entry jobs said.

Sharding is a scheduling change and it must not be a semantic one. The decisive test here
is `test_a_shard_writes_the_same_result_file_a_single_entry_job_would`: the same entry, the
same corpus tree and the same runner answers, verified once alone and once beside two
neighbours — one of which fails — must produce byte-identical result files. If that ever
stops holding, an entry's verdict has started depending on its runner company, and no
amount of green CI would tell you which verdict to believe.

Runs as a plain script (`python3 scripts/test_palomar_replay_shard.py`) so the Release
tooling workflow can execute it without pytest, and as a pytest module.
"""
from __future__ import annotations

import json
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import palomar_replay_shard as shard  # noqa: E402

GREEN_LOG = (
    "Exporting PalomarCorpus.E68.Challenge\n"
    "nanoda kernel accepts the solution\n"
    "Lean default kernel accepts the solution\n"
)
RED_LOG = "Exporting things\nsomething went wrong\n"
CLOCK = "2026-09-22T03:00:00Z"


def make_corpus(root: Path, entries: dict[str, int]) -> Path:
    """A corpus tree with one directory per entry. The value is a theorem count."""
    for entry, count in entries.items():
        directory = root / "PalomarCorpus" / entry
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "Challenge.lean").write_text(
            f"import Mathlib\n-- challenge for {entry}\n", encoding="utf-8")
        (directory / "comparator.json").write_text(json.dumps({
            "challenge_module": f"PalomarCorpus.{entry}.Challenge",
            "solution_module": f"Solutions.PalomarCorpus.{entry}",
            "theorem_names": [f"PalomarCorpus.{entry}.Challenge.thm_{i}" for i in range(count)],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        }, indent=2) + "\n", encoding="utf-8")
        (directory / "formalization.yaml").write_text(f"entry: {entry}\n", encoding="utf-8")
        solution = root / "Solutions" / "PalomarCorpus" / entry
        solution.mkdir(parents=True, exist_ok=True)
        (solution / "Statement.lean").write_text(f"-- solution for {entry}\n", encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    return root


def context(**overrides) -> dict:
    payload = {
        "github": {"sha": "a" * 40, "ref": "refs/heads/palomar/x",
                   "repository": "wcook04/plectis-erdos-lean", "run_id": "35674034595",
                   "run_attempt": "1", "workflow": "Palomar Comparator replay"},
        "lean_toolchain": "leanprover/lean4:v4.30.0",
        "comparator_lean_toolchain": "leanprover/lean4:v4.29.0",
        "tool_revisions": {"comparator": "c" * 40, "lean4export": "l" * 40,
                           "landrun": "d" * 40, "nanoda": "n" * 40, "renderer": "r" * 40},
        "sandbox_mode": "user-manager",
        "comparator_bin": "/tmp/comparator",
        "landrun": "/tmp/landrun",
        "nanoda": "/tmp/nanoda",
        "lean4export": "/tmp/lean4export",
        "audit_script": "/tmp/core_notation_audit.lean",
        "working_directory": "/work",
        "path": "/usr/bin:/bin",
        "user": "runner",
        "group": "docker",
    }
    payload.update(overrides)
    return payload


def fake_runner(outcomes: dict[str, dict]):
    """A runner whose answers are fixed per entry, so a result is fully determined.

    Each entry maps to `{"comparator_rc": int, "log": str, "challenge_rc": int,
    "solution_rc": int, "audit_rc": int}`; every stage also reports fixed seconds, so the
    timings a result records are deterministic and can be compared byte for byte.
    """
    def runner(stage, argv, *, log_path=None, env=None):
        if argv is None:
            return {"returncode": 125, "seconds": 0.0, "log": None}
        entry = next((part.split("/")[1] for part in argv
                      if part.startswith("PalomarCorpus/")), None)
        if entry is None:
            entry = next((part.rsplit(".", 2)[-2] for part in argv
                          if part.startswith("PalomarCorpus.")
                          or part.startswith("Solutions.PalomarCorpus.")), None)
        spec = outcomes.get(entry, {})
        if stage == shard.STAGE_CHALLENGE:
            rc, text, seconds = spec.get("challenge_rc", 0), "built\n", 7.0
        elif stage == shard.STAGE_SOLUTION:
            rc, text, seconds = spec.get("solution_rc", 0), "built\n", 11.0
        elif stage == shard.STAGE_COMPARATOR:
            rc, text, seconds = spec.get("comparator_rc", 0), spec.get("log", GREEN_LOG), 52.0
        else:
            rc, text, seconds = spec.get("audit_rc", 0), "audited\n", 9.0
        if log_path is not None:
            Path(log_path).parent.mkdir(parents=True, exist_ok=True)
            Path(log_path).write_text(text, encoding="utf-8")
        return {"returncode": rc, "seconds": seconds, "log": text}
    return runner


def clock() -> str:
    return CLOCK


# ------------------------------------------------------------------- the decisive test


def test_a_shard_writes_the_same_result_file_a_single_entry_job_would():
    """One entry, verified alone and verified beside a failing neighbour: same bytes.

    This is the whole warrant for sharding. The shard is deliberately hostile: E68 runs
    second, after an entry whose Comparator went red, and before another passing entry.
    """
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        corpus = make_corpus(root / "corpus", {"E68": 3, "E243": 2, "E257": 5})
        outcomes = {
            "E243": {"comparator_rc": 1, "log": RED_LOG},
            "E68": {"comparator_rc": 0, "log": GREEN_LOG},
            "E257": {"comparator_rc": 0, "log": GREEN_LOG},
        }
        alone = root / "alone"
        shard.run_shard("shard-01", ["E68"], corpus_root=corpus, out_dir=alone,
                        runner=fake_runner(outcomes), context=context(), now=clock)
        together = root / "together"
        manifest = shard.run_shard(
            "shard-07", ["E243", "E68", "E257"], corpus_root=corpus, out_dir=together,
            runner=fake_runner(outcomes), context=context(), now=clock)

        one = (alone / "receipt-E68.json").read_bytes()
        many = (together / "receipt-E68.json").read_bytes()
        assert one == many, "E68's result changed because of the entries beside it"
        assert b"shard-01" not in one and b"shard-07" not in many, \
            "a result file must not record which shard carried it"
        # The neighbour's failure is recorded, and only against the neighbour.
        assert json.loads(one)["exit"] == 0
        assert json.loads((together / "receipt-E243.json").read_text())["exit"] == 1
        assert json.loads((together / "receipt-E257.json").read_text())["exit"] == 0
        assert manifest["failed_entries"] == ["E243"]
        assert manifest["complete"] is True and manifest["all_passed"] is False


def test_a_failing_entry_does_not_stop_the_entries_after_it():
    with tempfile.TemporaryDirectory() as tmp:
        corpus = make_corpus(Path(tmp) / "corpus", {"E68": 1, "E243": 1, "E257": 1})
        outcomes = {
            "E68": {"challenge_rc": 1},
            "E243": {"comparator_rc": 1, "log": RED_LOG},
            "E257": {"comparator_rc": 0, "log": GREEN_LOG},
        }
        out = Path(tmp) / "out"
        manifest = shard.run_shard("shard-01", ["E68", "E243", "E257"], corpus_root=corpus,
                                   out_dir=out, runner=fake_runner(outcomes),
                                   context=context(), now=clock)
        assert manifest["delivered_entries"] == ["E68", "E243", "E257"]
        assert manifest["missing_entries"] == []
        assert manifest["failed_entries"] == ["E243", "E68"]
        assert manifest["complete"] is True and manifest["all_passed"] is False
        # A build failure means the Comparator never ran, so it reports no verdict. A null
        # exit is what the single-entry workflow's always-run receipt step recorded, and the
        # reconciliation reads it as a comparison failure.
        blocked = json.loads((out / "receipt-E68.json").read_text())
        assert blocked["exit"] is None and blocked["process_exit"] is None
        assert blocked["verification"] == {"outcome": "failed",
                                           "failure_stage": "build_challenge", "error": None}
        assert [row["stage"] for row in blocked["stages"]] == ["build_challenge"]


def test_an_entry_that_cannot_be_read_still_produces_a_result_file():
    """A promised entry never goes silently absent, whatever is wrong with it."""
    with tempfile.TemporaryDirectory() as tmp:
        corpus = make_corpus(Path(tmp) / "corpus", {"E68": 1, "E243": 1})
        (corpus / "PalomarCorpus/E243/comparator.json").write_text("{ not json",
                                                                   encoding="utf-8")
        out = Path(tmp) / "out"
        manifest = shard.run_shard("shard-01", ["E68", "E243"], corpus_root=corpus,
                                   out_dir=out, runner=fake_runner({}), context=context(),
                                   now=clock)
        assert manifest["complete"] is True and manifest["all_passed"] is False
        broken = json.loads((out / "receipt-E243.json").read_text())
        assert broken["schema"] == shard.RECEIPT_SCHEMA and broken["entry"] == "E243"
        assert broken["exit"] is None
        assert broken["verification"]["failure_stage"] == "read_comparator_config"
        assert "JSONDecodeError" in broken["verification"]["error"]


def test_an_entry_whose_directory_is_gone_is_named_not_dropped():
    with tempfile.TemporaryDirectory() as tmp:
        corpus = make_corpus(Path(tmp) / "corpus", {"E68": 1, "E243": 1})
        shutil.rmtree(corpus / "PalomarCorpus/E243")
        out = Path(tmp) / "out"
        manifest = shard.run_shard("shard-01", ["E68", "E243"], corpus_root=corpus,
                                   out_dir=out, runner=fake_runner({}), context=context(),
                                   now=clock)
        assert manifest["missing_entries"] == []
        assert manifest["failed_entries"] == ["E243"]
        assert json.loads((out / "receipt-E243.json").read_text())["entry"] == "E243"


def test_a_shard_with_no_usable_sandbox_reports_it_per_entry():
    with tempfile.TemporaryDirectory() as tmp:
        corpus = make_corpus(Path(tmp) / "corpus", {"E68": 1})
        out = Path(tmp) / "out"
        manifest = shard.run_shard(
            "shard-01", ["E68"], corpus_root=corpus, out_dir=out,
            runner=fake_runner({}), context=context(sandbox_mode="unavailable"), now=clock)
        assert manifest["all_passed"] is False
        receipt = json.loads((out / "receipt-E68.json").read_text())
        assert receipt["sandbox_mode"] == "unavailable" and receipt["exit"] == 125
        assert "refusing an insecure fallback" in (out / "E68.log").read_text()


# -------------------------------------------------------------------- the verdict rule


def test_a_green_process_exit_without_both_kernel_lines_is_not_green():
    assert shard.classify_comparator(0, GREEN_LOG)["exit"] == 0
    only_lean = "Lean default kernel accepts the solution\n"
    assert shard.classify_comparator(0, only_lean)["exit"] == 90
    only_nanoda = "nanoda kernel accepts the solution\n"
    assert shard.classify_comparator(0, only_nanoda)["exit"] == 91
    assert shard.classify_comparator(0, "")["exit"] == 90
    # A red process exit is reported as it stands; the kernel guards never soften it.
    red = shard.classify_comparator(4, GREEN_LOG)
    assert red["exit"] == 4 and red["process_exit"] == 4


def test_the_comparator_command_is_the_one_the_single_entry_workflow_ran():
    common = dict(config="PalomarCorpus/E68/comparator.json", comparator_bin="/t/comparator",
                  working_directory="/work", path="/usr/bin", landrun="/t/landrun",
                  nanoda="/t/nanoda", lean4export="/t/lean4export")
    user = shard.comparator_argv(sandbox_mode="user-manager", **common)
    assert user[:6] == ["timeout", "45m", "systemd-run",
                        "--property=RestrictAddressFamilies=~AF_UNIX", "--user", "--pipe"]
    assert user[-5:] == ["--working-directory=/work", "--", "lake", "env", "/t/comparator"] \
        or user[-4:] == ["lake", "env", "/t/comparator", "PalomarCorpus/E68/comparator.json"]
    system = shard.comparator_argv(sandbox_mode="system-manager-nonprivileged-unit",
                                   user="runner", group="docker", **common)
    assert system[:4] == ["timeout", "45m", "sudo", "-n"]
    assert "--uid=runner" in system and "--gid=docker" in system
    assert shard.comparator_argv(sandbox_mode="unavailable", **common) is None


def test_the_render_audit_command_repeats_the_theorem_keyword_per_name():
    argv = shard.render_audit_argv(audit_script="/t/a.lean", module="PalomarCorpus.E68.Challenge",
                                   theorem_names=["a", "b"])
    assert argv == ["timeout", "20m", "lake", "env", "lean", "--run", "/t/a.lean",
                    "PalomarCorpus.E68.Challenge", "theorem", "a", "theorem", "b"]


def test_a_result_records_the_solution_bytes_that_were_compared():
    with tempfile.TemporaryDirectory() as tmp:
        corpus = make_corpus(Path(tmp) / "corpus", {"E68": 1})
        out = Path(tmp) / "out"
        shard.run_shard("shard-01", ["E68"], corpus_root=corpus, out_dir=out,
                        runner=fake_runner({}), context=context(), now=clock)
        first = json.loads((out / "receipt-E68.json").read_text())["solution"]
        assert list(first["files"]) == ["Solutions/PalomarCorpus/E68/Statement.lean"]
        (corpus / "Solutions/PalomarCorpus/E68/Statement.lean").write_text("-- changed\n",
                                                                           encoding="utf-8")
        second_out = Path(tmp) / "out2"
        shard.run_shard("shard-01", ["E68"], corpus_root=corpus, out_dir=second_out,
                        runner=fake_runner({}), context=context(), now=clock)
        second = json.loads((second_out / "receipt-E68.json").read_text())["solution"]
        assert first["sha256"] != second["sha256"]


# ------------------------------------------------------------------------ the scheduler


def test_the_shard_budget_is_a_guarantee_not_an_aspiration():
    entries = [f"E257{chr(97 + i // 26)}{chr(97 + i % 26)}" for i in range(250)]
    plan = shard.plan_shards(entries, entry_seconds={name: 1200.0 for name in entries},
                             target_seconds=1800, max_shards=20, heavy_seconds=900)
    assert len(plan) <= 20
    assert sorted(e for row in plan for e in row["entries"]) == sorted(entries)


def test_an_unusually_heavy_entry_gets_a_shard_of_its_own():
    entries = ["E68", "E243", "E249", "E251", "E257"]
    plan = shard.plan_shards(
        entries, entry_seconds={"E249": 1400.0, "E68": 100.0, "E243": 100.0,
                                "E251": 100.0, "E257": 100.0},
        target_seconds=1800, max_shards=10, heavy_seconds=900)
    isolated = [row for row in plan if row["isolated"]]
    assert [row["entries"] for row in isolated] == [["E249"]]
    assert all(row["estimated_seconds"] <= 1800 for row in plan if not row["isolated"])


def test_the_plan_is_deterministic_and_covers_every_entry_exactly_once():
    entries = [f"E249{chr(97 + i)}" for i in range(20)] + ["E68", "E1049"]
    seconds = {name: 60.0 * (index % 7 + 1) for index, name in enumerate(entries)}
    first = shard.plan_shards(entries, entry_seconds=seconds, target_seconds=300, max_shards=40)
    second = shard.plan_shards(list(reversed(entries)), entry_seconds=seconds,
                               target_seconds=300, max_shards=40)
    assert first == second
    flat = [entry for row in first for entry in row["entries"]]
    assert sorted(flat) == sorted(entries) and len(flat) == len(set(flat))


def test_no_durations_sidecar_falls_back_to_equal_size_shards():
    with tempfile.TemporaryDirectory() as tmp:
        assert shard.load_durations(Path(tmp) / "absent.json")["entry_seconds"] == {}
        wrong = Path(tmp) / "wrong.json"
        wrong.write_text(json.dumps({"schema": "something_else", "entry_seconds": {"E68": 9}}),
                         encoding="utf-8")
        assert shard.load_durations(wrong)["entry_seconds"] == {}
        entries = [f"E249{chr(97 + i)}" for i in range(12)]
        plan = shard.plan_shards(entries, entry_seconds={}, default_seconds=300,
                                 target_seconds=900, max_shards=10)
        assert sorted(row["entry_count"] for row in plan) == [3, 3, 3, 3]


def test_a_shard_id_maps_back_to_the_entries_it_promised():
    entries = ["E68", "E243", "E249"]
    plan = {"shards": shard.plan_shards(entries, target_seconds=10_000, max_shards=4),
            "entries": sorted(entries)}
    mapping = shard.shard_map(plan)
    assert sorted(entry for group in mapping.values() for entry in group) == sorted(entries)
    assert shard.shard_entries(plan, next(iter(mapping)))


# ----------------------------------------------------------------------- run coverage


def _plan_for(entries: list[str]) -> dict:
    return {"schema": shard.PLAN_SCHEMA, "entries": sorted(entries),
            "shards": shard.plan_shards(entries, target_seconds=10_000, max_shards=4)}


def _deliver(directory: Path, entry: str, *, artifact: str = "palomar-comparator-replay-shard-01",
             green: bool = True) -> None:
    place = directory / artifact
    place.mkdir(parents=True, exist_ok=True)
    (place / f"receipt-{entry}.json").write_text(json.dumps({
        "schema": shard.RECEIPT_SCHEMA, "entry": entry,
        "exit": 0 if green else 1, "process_exit": 0 if green else 1,
        "kernel_acceptance": {"lean_default": green, "nanoda": green},
    }) + "\n", encoding="utf-8")


def test_a_promised_entry_with_no_result_file_fails_the_run():
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        for entry in ("E68", "E243"):
            _deliver(out, entry)
        report = shard.check_run_coverage(_plan_for(["E68", "E243", "E257"]), out)
        assert report["ok"] is False and report["missing_entries"] == ["E257"]
        assert "delivered no result file" in report["problems"][0]


def test_a_red_entry_inside_a_shard_fails_the_run():
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        _deliver(out, "E68")
        _deliver(out, "E243", green=False)
        report = shard.check_run_coverage(_plan_for(["E68", "E243"]), out)
        assert report["ok"] is False and report["red_entries"] == ["E243"]


def test_a_plan_built_for_another_population_fails_the_run():
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        for entry in ("E68", "E243"):
            _deliver(out, entry)
        report = shard.check_run_coverage(_plan_for(["E68", "E243"]), out,
                                          expected_entries=["E68", "E243", "E999"])
        assert report["ok"] is False
        assert "different entry population" in report["problems"][0]


def test_a_complete_green_run_passes():
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        for index, entry in enumerate(("E68", "E243", "E257")):
            _deliver(out, entry, artifact=f"palomar-comparator-replay-shard-0{index}")
        report = shard.check_run_coverage(_plan_for(["E68", "E243", "E257"]), out,
                                          expected_entries=["E68", "E243", "E257"])
        assert report["ok"] is True and report["problems"] == []
        assert report["promised"] == report["delivered"] == 3


def main() -> int:
    tests = [value for name, value in sorted(globals().items()) if name.startswith("test_")]
    failures = 0
    for test in tests:
        try:
            test()
        except AssertionError as error:
            print(f"FAIL {test.__name__}: {error}")
            failures += 1
        except Exception as error:  # noqa: BLE001
            print(f"ERROR {test.__name__}: {type(error).__name__}: {error}")
            failures += 1
        else:
            print(f"ok   {test.__name__}")
    print(f"\n{len(tests) - failures}/{len(tests)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
