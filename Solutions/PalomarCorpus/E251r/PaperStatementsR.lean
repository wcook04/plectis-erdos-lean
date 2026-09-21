/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.ShiftedGapCountingR9
import Solutions.PalomarCorpus.E251r.Statement

open Filter
open Topology
open Finset
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsR

theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := @ErdosProblems.Erdos251.PaperR9.ShiftCounting.shifted_count_bound h N H hh r

end PalomarCorpus.E251.PaperStatementsR
