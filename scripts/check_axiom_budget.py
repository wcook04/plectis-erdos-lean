#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Diff the axioms a build log actually printed against each entry's permitted set.

Every entry's ``AxiomAudit.lean`` is inside that entry's Lake library glob, so a
release build elaborates all of them and their ``#print axioms`` output lands in
the log. ``#print axioms`` prints; it does not fail a build when a printed axiom
falls outside ``comparator.json::permitted_axioms``. This script closes that gap
after the fact: give it a build log and it reports, per entry, whether every
compared declaration was printed and whether any printed axiom is outside the
entry's declared budget.

    gh run view <run-id> --repo wcook04/plectis-erdos-lean --log > run.log
    python3 scripts/check_axiom_budget.py --log run.log

Exit 0 when every compared declaration was printed and no printed axiom is
outside its budget. Exit 1 otherwise, naming what is missing or over budget.

For ``--log``, the evidence is the log. This mode does not run Lean, and a log from a
different commit proves nothing about this one. ``--expect-commit`` checks
that the *checkout* whose comparator.json files are read is the commit you
mean; it cannot establish which commit produced a supplied log, so a
``--log`` report carries ``source_binding.mode = "log_only"`` and names the
checkout it was parsed in. ``--run-palomar`` uses ``lake lean`` on each audit
file, so Lake builds its Solution import closure from the current checkout
before Lean queries the axioms. Its before/after source fingerprint also
rejects a checkout changed during the audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import palomar_entry_names  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
ENTRY_PREFIX = "ExternalVerification"
PALOMAR_PROBLEMS = palomar_entry_names.PROBLEMS

# 'Namespace.decl' depends on axioms: [a, b, c]
# Lean wraps a long axiom list over several lines, so the list may span newlines.
AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOM_LINE = re.compile(r"'([^']+)' does not depend on any axioms")

# `gh run view --log` prefixes every line with "<job>\t<step>\t<ISO timestamp> ".
# The prefix has to come off before the wrapped axiom lists are rejoined, or each
# continuation line contributes its own prefix to the axiom set.
GH_LOG_PREFIX = re.compile(r"^[^\t]*\t[^\t]*\t\d{4}-\d\d-\d\dT[\d:.]+Z ?", re.M)


def strip_log_prefixes(text: str) -> str:
    return GH_LOG_PREFIX.sub("", text)


def parse_log(text: str) -> dict[str, set[str]]:
    """Map declaration name to the set of axioms the log printed for it.

    A declaration printed more than once (the workflow builds targets one at a
    time and shared modules are re-reported) contributes the union, so a single
    over-budget print cannot be hidden by a later clean one.
    """
    text = strip_log_prefixes(text)
    printed: dict[str, set[str]] = {}
    for name in NO_AXIOM_LINE.findall(text):
        printed.setdefault(name, set())
    for name, axioms in AXIOM_LINE.findall(text):
        found = {a.strip() for a in axioms.split(",") if a.strip()}
        printed.setdefault(name, set()).update(found)
    return printed


def entries(*, palomar: bool = False) -> list[str]:
    """The publication entries (with ``palomar``), else the family directories.

    The publication set is every ``PalomarCorpus/E*`` configuration, checked as a whole by
    ``scripts/palomar_entry_names.py``: the paper-order ``E<problem>_<NN>`` entries, or in a
    retired tree the eight problem entries with their bands. It used to be exactly the eight
    problem entries, so no band, and no entry since the paper-order re-pack, was ever audited.
    """
    if palomar:
        if (REPO_ROOT / "PalomarCorpus/comparator.json").exists():
            raise ValueError("the superseded flat PalomarCorpus/comparator.json is present")
        return [f"PalomarCorpus/{name}" for name in palomar_entry_names.discover(REPO_ROOT)]
    return sorted(
        p.name for p in REPO_ROOT.iterdir() if p.is_dir() and p.name.startswith(ENTRY_PREFIX)
    )


def source_identity() -> dict:
    """Fingerprint the worktree bytes the built environments can have consumed.

    Tracked and untracked-but-not-ignored files both count (a new proof module that is
    not yet committed still participates in the build), a path deleted in the worktree is
    skipped and recorded, and ``worktree_clean`` says whether the fingerprint is the
    committed tree at ``commit`` or a working state ahead of it.
    """
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=REPO_ROOT
    ).decode().split("\0")
    selected = sorted(path for path in set(paths) if path and (
        path.endswith(".lean") or path.endswith("/comparator.json")
        or path in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}))
    hashes = {}
    deleted = []
    for path in selected:
        full = REPO_ROOT / path
        if full.is_file():
            hashes[path] = hashlib.sha256(full.read_bytes()).hexdigest()
        else:
            deleted.append(path)
    status = subprocess.check_output(["git", "status", "--porcelain"], cwd=REPO_ROOT).decode()
    return {
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT).decode().strip(),
        "worktree_clean": status.strip() == "",
        "source_file_count": len(hashes),
        "deleted_in_worktree": deleted,
        "source_files_sha256": hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest(),
        "scope": "tracked and untracked-not-ignored Lean sources, Comparator configurations, Lake configuration and dependency lock, as present in the worktree",
    }


def run_palomar_audits(entry_paths: list[str], progress_file: Path | None = None) -> tuple[str, dict, list[dict]]:
    """Audit the entire planned population, retaining failures at each entry."""
    before = source_identity()
    outputs = []
    seen = set()
    specifications = []
    outcomes: list[dict] = []

    def write_progress() -> None:
        if progress_file is None:
            return
        progress_file.parent.mkdir(parents=True, exist_ok=True)
        pending = [{"entry": entry, "status": "not_attempted"}
                   for entry in entry_paths[len(outcomes):]]
        payload = {"schema": "palomar_axiom_audit_progress_v1", "source_before": before,
                   "planned_entries": entry_paths, "outcomes": outcomes + pending}
        temporary = progress_file.with_suffix(progress_file.suffix + ".tmp")
        temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        temporary.replace(progress_file)

    write_progress()
    # Validate the entire population before building any member. The progress
    # artifact survives preflight failure with every promised entry accounted for.
    for entry in entry_paths:
        try:
            root = REPO_ROOT / entry
            config = json.loads((root / "comparator.json").read_text())
            if not isinstance(config, dict):
                raise ValueError(f"Comparator must be an object: {entry}")
            problem = root.name
            if (config.get("challenge_module") != f"PalomarCorpus.{problem}.Challenge"
                    or config.get("solution_module") != f"Solutions.PalomarCorpus.{problem}"):
                raise ValueError(f"incorrect Challenge/Solution modules: {entry}")
            challenge = (root / "Challenge.lean").read_bytes()
            if len(challenge) > 102400 or len(challenge.splitlines()) > 1000:
                raise ValueError(f"Challenge exceeds a hard publication limit: {entry}")
            imports = re.findall(r"^import\s+(\S+)", challenge.decode(), re.M)
            if not imports or any(name != "Mathlib" and not name.startswith("Mathlib.") for name in imports):
                raise ValueError(f"Challenge must import only Mathlib: {entry}")
            names = config.get("theorem_names") or []
            if (not isinstance(names, list) or not names
                    or any(not isinstance(name, str) or not name for name in names)
                    or len(set(names)) != len(names) or seen.intersection(names)):
                raise ValueError(f"empty or duplicated selected theorem identities: {entry}")
            seen.update(names)
            specifications.append((entry, problem, config["solution_module"], names))
        except (OSError, ValueError, UnicodeError, TypeError) as error:
            outcomes[:] = [{"entry": path, "status": "invalid" if path == entry else "not_attempted",
                            **({"error": str(error)} if path == entry else {})}
                           for path in entry_paths]
            write_progress()
            raise
    with tempfile.TemporaryDirectory(prefix="plectis-axiom-audit-") as directory:
        for entry, problem, solution_module, names in specifications:
            audit = Path(directory) / f"{problem}.lean"
            audit.write_text("import " + solution_module + "\n\n"
                             + "\n".join("#print axioms " + name for name in names) + "\n")
            # `lake env lean` only imports whatever .olean is already present.
            # `lake lean` first builds this file's imports, including the current
            # Solution proof, so a cold or stale cache cannot supply the verdict.
            try:
                result = subprocess.run(["lake", "lean", str(audit)], cwd=REPO_ROOT,
                                        text=True, capture_output=True, timeout=600)
                output = result.stdout + result.stderr
                outcome = {"entry": entry, "status": "pass" if result.returncode == 0 else "fail",
                           "returncode": result.returncode}
            except subprocess.TimeoutExpired as error:
                def decoded(part: str | bytes | None) -> str:
                    return part.decode("utf-8", "replace") if isinstance(part, bytes) else (part or "")
                output = decoded(error.stdout) + decoded(error.stderr)
                outcome = {"entry": entry, "status": "timeout", "returncode": None}
            except OSError as error:
                output = str(error)
                outcome = {"entry": entry, "status": "runner_error", "returncode": None}
            outcome["output_sha256"] = hashlib.sha256(output.encode("utf-8", "replace")).hexdigest()
            if outcome["status"] != "pass":
                print(f"Solution audit {outcome['status']} for {entry}:\n{output}", file=sys.stderr)
            outputs.append(output)
            outcomes.append(outcome)
            write_progress()
    after = source_identity()
    source_keys = ("commit", "source_file_count", "deleted_in_worktree", "source_files_sha256")
    stable = all(after[key] == before[key] for key in source_keys)
    binding = {"mode": "fresh_lake_lean", "source_before": before, "source_after": after,
               "source_stable": stable}
    if not stable:
        print("proof inputs changed while the publication audit was running", file=sys.stderr)
    return "\n".join(outputs), binding, outcomes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", help="build log to read (- for stdin)")
    parser.add_argument("--run-palomar", action="store_true",
                        help="run fresh axiom audits of every built publication entry's Solution environment")
    parser.add_argument("--progress-file", type=Path,
                        help="atomically retain entry outcomes during --run-palomar")
    parser.add_argument("--expect-commit", help="fail unless HEAD is this commit")
    parser.add_argument("--json", action="store_true", help="emit the report as JSON")
    args = parser.parse_args()
    if bool(args.log) == bool(args.run_palomar):
        parser.error("choose exactly one of --log and --run-palomar")

    if args.expect_commit:
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True
        ).stdout.strip()
        if head != args.expect_commit:
            print(f"HEAD is {head}, expected {args.expect_commit}", file=sys.stderr)
            return 1

    selected_entries = entries(palomar=args.run_palomar)
    if args.run_palomar:
        text, binding, outcomes = run_palomar_audits(selected_entries, args.progress_file)
    else:
        if args.progress_file:
            parser.error("--progress-file requires --run-palomar")
        outcomes = []
        text = sys.stdin.read() if args.log == "-" else Path(args.log).read_text(
            encoding="utf-8", errors="replace"
        )
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True
        ).stdout.strip()
        # A parsed log establishes what it printed, not which source produced it;
        # the checkout only supplies the comparator.json budgets it is compared against.
        binding = {
            "mode": "log_only",
            "log_sha256": hashlib.sha256(text.encode("utf-8", "replace")).hexdigest(),
            "budgets_read_from_checkout": head,
            "producer": "not established by this parser",
        }
    printed = parse_log(text)

    rows = []
    ok = True
    for index, entry in enumerate(selected_entries):
        comparator = json.loads((REPO_ROOT / entry / "comparator.json").read_text(encoding="utf-8"))
        permitted = set(comparator.get("permitted_axioms") or [])
        missing, over = [], []
        for name in comparator.get("theorem_names") or []:
            if name not in printed:
                missing.append(name)
                continue
            extra = sorted(printed[name] - permitted)
            if extra:
                over.append({"declaration": name, "axioms_outside_budget": extra})
        execution = outcomes[index] if args.run_palomar else None
        status = "ok" if not missing and not over and (execution is None or execution["status"] == "pass") else "failed"
        ok = ok and status == "ok"
        rows.append(
            {
                "entry": entry,
                "status": status,
                "execution": execution,
                "permitted_axioms": sorted(permitted),
                "declarations_compared": len(comparator.get("theorem_names") or []),
                "declarations_not_printed_in_log": missing,
                "declarations_over_budget": over,
            }
        )

    report = {
        "schema": "plectis_erdos_lean_axiom_budget_check_v1",
        "log": args.log,
        "entries_checked": len(rows),
        "declarations_printed_in_log": len(printed),
        "sorry_ax_printed": "sorryAx" in text,
        "status": "ok" if ok and "sorryAx" not in text and (not args.run_palomar or binding["source_stable"]) else "failed",
        "entries": rows,
        "planned_entries": selected_entries if args.run_palomar else None,
        "source_binding": binding,
        "does_not_establish": ["Comparator equivalence", "NanoDa verification", "Palomar registration"],
    }
    if "sorryAx" in text:
        ok = False
    if args.run_palomar and not binding["source_stable"]:
        ok = False

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"declarations printed in log: {report['declarations_printed_in_log']}")
        print(f"sorryAx printed: {report['sorry_ax_printed']}")
        for row in rows:
            print(f"  {row['status']:6s} {row['entry']} ({row['declarations_compared']} compared)")
            for name in row["declarations_not_printed_in_log"]:
                print(f"           not printed: {name}")
            for item in row["declarations_over_budget"]:
                print(f"           over budget: {item['declaration']} {item['axioms_outside_budget']}")
        print(f"status: {report['status']}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
