#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The names of the Palomar publication entries, for every tool here that discovers them.

The entries are ``PalomarCorpus/E<problem>_<NN>``: each problem's theorems in the order its
papers state them, with ``NN`` counting from ``01`` without a gap. A tree from before that
layout holds the eight problem entries ``E<problem>`` and their letter bands
``E<problem><letters>``; it is still read, but the two layouts never mix in one tree.

The replay workflow's inventory and aggregate steps, the shard planner and the release
axiom audit all read the entry set through ``discover`` so they cannot disagree about it.
Standard library only.
"""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
_ALT = "|".join(str(number) for number in PROBLEMS)
PAPER_ORDER_RE = re.compile(rf"^E({_ALT})_(\d{{2,3}})$")
PROBLEM_BAND_RE = re.compile(rf"^E({_ALT})([a-z]{{1,2}})?$")

PAPER_ORDER = "paper_order"
PROBLEM_BANDS = "problem_bands"


def check_entry_names(names: list[str]) -> str:
    """The layout the names form; ValueError for a stray, a mixture, a gap or a missing problem."""
    names = list(names)
    paper_order = [name for name in names if PAPER_ORDER_RE.match(name)]
    problem_bands = [name for name in names if PROBLEM_BAND_RE.match(name)]
    stray = sorted(set(names) - set(paper_order) - set(problem_bands))
    if stray:
        raise ValueError(f"unrecognised PalomarCorpus entries: {stray}")
    if paper_order and problem_bands:
        raise ValueError(
            "paper-order entries and problem or band entries are mixed: "
            f"{sorted(problem_bands)[:6]}"
        )
    if paper_order:
        numbers: dict[int, list[int]] = defaultdict(list)
        for name in paper_order:
            match = PAPER_ORDER_RE.match(name)
            numbers[int(match.group(1))].append(int(match.group(2)))
        missing = [problem for problem in PROBLEMS if problem not in numbers]
        if missing:
            raise ValueError(f"no paper-order PalomarCorpus entry for problems {missing}")
        gaps = {
            problem: sorted(found)
            for problem, found in numbers.items()
            if sorted(found) != list(range(1, len(found) + 1))
        }
        if gaps:
            raise ValueError(f"paper-order entry numbers must run from 01 without a gap or repeat: {gaps}")
        return PAPER_ORDER
    missing = [f"E{number}" for number in PROBLEMS if f"E{number}" not in names]
    if missing:
        raise ValueError(f"missing base PalomarCorpus entries: {missing}")
    return PROBLEM_BANDS


def sort_key(name: str) -> tuple:
    """Problem order, then paper order (or band order in a retired tree)."""
    match = PAPER_ORDER_RE.match(name)
    if match:
        return (PROBLEMS.index(int(match.group(1))), int(match.group(2)), name)
    match = PROBLEM_BAND_RE.match(name)
    if match:
        band = match.group(2) or ""
        return (PROBLEMS.index(int(match.group(1))), len(band), band)
    return (len(PROBLEMS), 0, name)


def discover(corpus_root: Path | str = ".") -> list[str]:
    """Every publication entry in the tree, in problem and paper order, once checked."""
    found = [
        path.parent.name
        for path in Path(corpus_root, "PalomarCorpus").glob("E*/comparator.json")
    ]
    check_entry_names(found)
    return sorted(found, key=sort_key)
