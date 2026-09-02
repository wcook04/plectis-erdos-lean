#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the machine-readable release manifest and SHA256SUMS for a tagged cut.

The manifest answers one question for a reader who has the tarball and not the
repository: for each Comparator entry, which configuration a registry submission
names, which files carry the statement and the proof, what those files hash to,
and what the entry's own metadata records about its axiom audit.

It reports recorded metadata verbatim. It does not run Lean, does not run a
Comparator replay, and therefore never asserts that an audit passed. Where an
entry's ``formalization.yaml`` records a pending or deferred audit status, that
string is what the manifest carries.

Usage:

    python3 scripts/build_release_manifest.py --out release-manifest.json \\
        --sums-out SHA256SUMS [--tag v0.1.0] [--commit <sha>]

Both outputs are release attachments, not repository content.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
ENTRY_PREFIX = "ExternalVerification"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git(*args: str) -> str | None:
    try:
        out = subprocess.run(
            ["git", *args], cwd=REPO_ROOT, capture_output=True, text=True, check=True
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.stdout.strip() or None


def yaml_scalar(text: str, key: str) -> str | None:
    """Read one flat ``key: value`` scalar without a YAML dependency.

    The generated formalization files are emitted by one writer with a flat
    scalar shape for these keys, so a line match is exact here. Anything the
    pattern does not match is reported as absent rather than guessed.
    """
    match = re.search(rf"^\s*{re.escape(key)}\s*:\s*(.+?)\s*$", text, re.M)
    if not match:
        return None
    value = match.group(1).strip()
    if value.startswith(("'", '"')) and value.endswith(("'", '"')) and len(value) > 1:
        value = value[1:-1]
    return value or None


def toolchain() -> str | None:
    path = REPO_ROOT / "lean-toolchain"
    return path.read_text(encoding="utf-8").strip() if path.is_file() else None


def mathlib_pin() -> dict[str, str] | None:
    path = REPO_ROOT / "lake-manifest.json"
    if not path.is_file():
        return None
    manifest = json.loads(path.read_text(encoding="utf-8"))
    for package in manifest.get("packages") or []:
        if package.get("name") == "mathlib":
            return {
                "rev": package.get("rev"),
                "inputRev": package.get("inputRev"),
                "url": package.get("url"),
            }
    return None


def entry_row(entry: str) -> dict[str, Any]:
    directory = REPO_ROOT / entry
    comparator_path = directory / "comparator.json"
    comparator = json.loads(comparator_path.read_text(encoding="utf-8"))

    challenge = directory / "Challenge.lean"
    solution = REPO_ROOT / "Solutions" / f"{entry}.lean"
    audit = directory / "AxiomAudit.lean"
    metadata = directory / "formalization.yaml"

    row: dict[str, Any] = {
        "entry": entry,
        "comparator_config_path": f"{entry}/comparator.json",
        "comparator_config_sha256": sha256_file(comparator_path),
        "challenge_module": comparator.get("challenge_module"),
        "solution_module": comparator.get("solution_module"),
        "theorem_names": comparator.get("theorem_names"),
        "permitted_axioms": comparator.get("permitted_axioms"),
        "challenge_path": f"{entry}/Challenge.lean",
        "challenge_sha256": sha256_file(challenge) if challenge.is_file() else None,
        "solution_path": f"Solutions/{entry}.lean" if solution.is_file() else None,
        "solution_sha256": sha256_file(solution) if solution.is_file() else None,
        "axiom_audit_path": f"{entry}/AxiomAudit.lean" if audit.is_file() else None,
        "axiom_audit_sha256": sha256_file(audit) if audit.is_file() else None,
    }

    negative = directory / "comparator-negative-mismatch.json"
    if negative.is_file():
        row["negative_comparator_config_path"] = f"{entry}/comparator-negative-mismatch.json"
        row["negative_comparator_config_sha256"] = sha256_file(negative)

    if metadata.is_file():
        text = metadata.read_text(encoding="utf-8")
        row["axiom_audit_status_recorded"] = yaml_scalar(text, "axiom_audit_status")
        row["formalization_metadata_path"] = f"{entry}/formalization.yaml"
        row["formalization_metadata_sha256"] = sha256_file(metadata)

    solution_text = solution.read_text(encoding="utf-8") if solution.is_file() else ""
    row["solution_contains_sorry"] = bool(re.search(r"\bsorry\b", solution_text))
    return row


def build(tag: str | None, commit: str | None) -> dict[str, Any]:
    entries = sorted(
        p.name for p in REPO_ROOT.iterdir() if p.is_dir() and p.name.startswith(ENTRY_PREFIX)
    )
    rows = [entry_row(entry) for entry in entries]
    return {
        "schema": "plectis_erdos_lean_release_manifest_v1",
        "what_this_is": (
            "Per-entry file identity for one tagged cut of wcook04/plectis-erdos-lean. "
            "Hashes are of the files at this commit. Axiom-audit status is the string the "
            "entry's own formalization metadata records; this manifest runs no Lean and no "
            "Comparator replay, so it never asserts that an audit or a replay passed."
        ),
        "axiom_audit_note": (
            "Each entry's AxiomAudit module is inside that entry's Lake library glob, so the "
            "release workflow elaborates all 21 of them and the #print axioms output appears in "
            "the build log. #print axioms prints; it does not fail a build when a printed axiom "
            "falls outside the entry's permitted_axioms. A green workflow therefore establishes "
            "that every Challenge, Solution and AxiomAudit module elaborates, not that the "
            "permitted-axiom budget was enforced. The recorded per-entry axiom_audit_status "
            "strings come from private metadata and several of them read as pending."
        ),
        "repository": "wcook04/plectis-erdos-lean",
        "tag": tag,
        "commit": commit or git("rev-parse", "HEAD"),
        "lean_toolchain": toolchain(),
        "mathlib": mathlib_pin(),
        "entry_count": len(rows),
        "problems": sorted(
            {re.sub(r"^" + ENTRY_PREFIX + r"(\d+).*$", r"\1", e) for e in entries}, key=int
        ),
        "entries": rows,
    }


def sha256sums(paths: list[Path]) -> str:
    lines = []
    for path in sorted(paths):
        rel = path.relative_to(REPO_ROOT).as_posix()
        lines.append(f"{sha256_file(path)}  {rel}")
    return "\n".join(lines) + "\n"


def tracked_files() -> list[Path]:
    listing = git("ls-files", "-z")
    if listing is None:
        raise SystemExit("git ls-files failed; run this inside a checkout")
    return [REPO_ROOT / name for name in listing.split("\0") if name]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="release-manifest.json")
    parser.add_argument("--sums-out", default="SHA256SUMS")
    parser.add_argument("--tag")
    parser.add_argument("--commit")
    args = parser.parse_args()

    manifest = build(args.tag, args.commit)
    Path(args.out).write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    Path(args.sums_out).write_text(sha256sums(tracked_files()), encoding="utf-8")

    print(f"entries: {manifest['entry_count']}")
    print(f"commit: {manifest['commit']}")
    print(f"manifest: {args.out}")
    print(f"sums: {args.sums_out}")
    sorries = [row["entry"] for row in manifest["entries"] if row["solution_contains_sorry"]]
    print(f"solutions containing sorry: {sorries or 'none'}")
    return 1 if sorries else 0


if __name__ == "__main__":
    raise SystemExit(main())
