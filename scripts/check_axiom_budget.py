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

The evidence is the log. This script does not run Lean, and a log from a
different commit proves nothing about this one -- pass ``--expect-commit`` to
bind the check to the commit you mean.
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

REPO_ROOT = Path(__file__).resolve().parent.parent
ENTRY_PREFIX = "ExternalVerification"
PALOMAR_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)

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
    if palomar:
        expected = {f"E{number}" for number in PALOMAR_PROBLEMS}
        found = {path.parent.name for path in (REPO_ROOT / "PalomarCorpus").glob("E*/comparator.json")}
        if found != expected or (REPO_ROOT / "PalomarCorpus/comparator.json").exists():
            raise ValueError("publication must contain exactly the eight problem-level configurations")
        return [f"PalomarCorpus/E{number}" for number in PALOMAR_PROBLEMS]
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


def run_palomar_audits(entry_paths: list[str]) -> tuple[str, dict]:
    """Inspect each built Solution environment separately from its Challenge."""
    before = source_identity()
    outputs = []
    seen = set()
    with tempfile.TemporaryDirectory(prefix="plectis-axiom-audit-") as directory:
        for entry in entry_paths:
            root = REPO_ROOT / entry
            config = json.loads((root / "comparator.json").read_text())
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
            if not names or len(set(names)) != len(names) or seen.intersection(names):
                raise ValueError(f"empty or duplicated selected theorem identities: {entry}")
            seen.update(names)
            audit = Path(directory) / f"{problem}.lean"
            audit.write_text("import " + config["solution_module"] + "\n\n"
                             + "\n".join("#print axioms " + name for name in names) + "\n")
            result = subprocess.run(["lake", "env", "lean", str(audit)], cwd=REPO_ROOT,
                                    text=True, capture_output=True, timeout=600)
            if result.returncode:
                raise RuntimeError(f"Solution audit failed for {entry}:\n{result.stdout}\n{result.stderr}")
            outputs.append(result.stdout + result.stderr)
    if source_identity() != before:
        raise RuntimeError("proof inputs changed while the publication audit was running")
    return "\n".join(outputs), before


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", help="build log to read (- for stdin)")
    parser.add_argument("--run-palomar", action="store_true",
                        help="run fresh axiom audits of the eight built publication Solution environments")
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
    binding = None
    if args.run_palomar:
        text, binding = run_palomar_audits(selected_entries)
    else:
        text = sys.stdin.read() if args.log == "-" else Path(args.log).read_text(
            encoding="utf-8", errors="replace"
        )
    printed = parse_log(text)

    rows = []
    ok = True
    for entry in selected_entries:
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
        status = "ok" if not missing and not over else "failed"
        ok = ok and status == "ok"
        rows.append(
            {
                "entry": entry,
                "status": status,
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
        "status": "ok" if ok and "sorryAx" not in text else "failed",
        "entries": rows,
        "source_binding": binding,
        "does_not_establish": ["Comparator equivalence", "NanoDa verification", "Palomar registration"],
    }
    if "sorryAx" in text:
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
