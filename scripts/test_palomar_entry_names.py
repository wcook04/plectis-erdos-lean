# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The entry names every discovery path reads: paper order, or the retired problem layout."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import palomar_entry_names as names  # noqa: E402

PAPER_ORDER = [f"E{n}_{i:02d}" for n in names.PROBLEMS for i in (1, 2)]
LEGACY = [f"E{n}" for n in names.PROBLEMS] + ["E257a", "E249ab"]


class EntryNamesTest(unittest.TestCase):
    def test_paper_order_names_are_one_layout(self):
        self.assertEqual(names.check_entry_names(PAPER_ORDER), names.PAPER_ORDER)

    def test_the_retired_layout_is_still_read(self):
        self.assertEqual(names.check_entry_names(LEGACY), names.PROBLEM_BANDS)

    def test_the_layouts_never_mix(self):
        with self.assertRaisesRegex(ValueError, "mixed"):
            names.check_entry_names(PAPER_ORDER + ["E68"])

    def test_a_gap_or_repeat_in_the_numbers_is_refused(self):
        with self.assertRaisesRegex(ValueError, "without a gap"):
            names.check_entry_names([name for name in PAPER_ORDER if name != "E68_01"] + ["E68_03"])
        with self.assertRaisesRegex(ValueError, "without a gap"):
            names.check_entry_names(PAPER_ORDER + ["E68_001"])

    def test_every_problem_needs_an_entry(self):
        with self.assertRaisesRegex(ValueError, "problems \\[1049\\]"):
            names.check_entry_names([name for name in PAPER_ORDER if not name.startswith("E1049_")])

    def test_strays_are_named(self):
        for stray in ("E70_01", "E68_1", "E68_0001", "E68-01", "E68A", "E68abc"):
            with self.assertRaisesRegex(ValueError, "unrecognised"):
                names.check_entry_names(PAPER_ORDER + [stray])

    def test_discovery_orders_by_problem_then_paper(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in PAPER_ORDER:
                entry = Path(tmp) / "PalomarCorpus" / name
                entry.mkdir(parents=True)
                (entry / "comparator.json").write_text(json.dumps({"theorem_names": ["x"]}))
            found = names.discover(tmp)
        self.assertEqual(found[:3], ["E68_01", "E68_02", "E243_01"])
        self.assertEqual(found[-1], "E1049_02")


if __name__ == "__main__":
    unittest.main()
