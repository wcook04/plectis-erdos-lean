/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DyadicBlockMassIdentity
import ErdosProblems.Erdos269.DyadicOrderedTailRecurrence
import ErdosProblems.Erdos269.PaperExactDenominatorR13
import ErdosProblems.Erdos269.PaperR7WindowResults
import ErdosProblems.Erdos269.RationalLatticeReduction
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import Solutions.PalomarCorpus.E269f.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsF

theorem firstClearingIndex_le_sufficient (u v w : ℕ) :
    firstClearingIndex u v w ≤ u + 1 + 2 * v + 3 * w := @ErdosProblems.Erdos269.PaperR13.firstClearingIndex_le_sufficient u v w

theorem firstClearingIndex_minimal {u v w a : ℕ} (ha : ClearingCondition u v w a) :
    firstClearingIndex u v w ≤ a := @ErdosProblems.Erdos269.PaperR13.firstClearingIndex_minimal u v w a ha

theorem firstClearingIndex_spec (u v w : ℕ) :
    ClearingCondition u v w (firstClearingIndex u v w) := @ErdosProblems.Erdos269.PaperR13.firstClearingIndex_spec u v w

theorem scaled_state_is_integer_iff_firstClearingIndex_le
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a) :
    (∃ z : ℤ,
      (B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a = (z : ℚ)) ↔
      firstClearingIndex u v w ≤ a := @ErdosProblems.Erdos269.PaperR13.scaled_state_is_integer_iff_firstClearingIndex_le N u v w B a hB hB30 hcop ha

theorem long_window_growth (lo len : ℕ) (_hlen : 1 ≤ len) :
    actualWindowBase lo len =
      ((2 ^ len *
        3 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 3 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 3 2⌋₊) *
        5 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 5 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 5 2⌋₊) : ℕ) : ℤ) ∧
    (8 : ℝ) ^ len / 15 < (actualWindowBase lo len : ℝ) ∧
    (actualWindowBase lo len : ℝ) < 15 * (8 : ℝ) ^ len := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperR7.long_window_growth lo len _hlen

end PalomarCorpus.E269.PaperStatementsF
