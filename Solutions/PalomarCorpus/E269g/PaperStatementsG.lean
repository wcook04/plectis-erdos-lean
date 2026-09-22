/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DyadicBlockMassIdentity
import ErdosProblems.Erdos269.DyadicBlockThresholdPartition
import ErdosProblems.Erdos269.DyadicOrderedTailRecurrence
import ErdosProblems.Erdos269.DyadicShellSummability
import ErdosProblems.Erdos269.IntegralBranchExtinction
import ErdosProblems.Erdos269.JumpConstraintMajorant
import ErdosProblems.Erdos269.PaperCompleteR20.RealBoundDenominatorReduction
import ErdosProblems.Erdos269.PaperExactDenominatorR13
import ErdosProblems.Erdos269.PaperR7SeriesIdentification
import ErdosProblems.Erdos269.PaperR7WindowResults
import ErdosProblems.Erdos269.RationalLatticeReduction
import ErdosProblems.Erdos269.ResidueEscape
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import Solutions.PalomarCorpus.E269g.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsG

theorem conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound c d b m s B hs hfactor hrec

theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a) := @ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing N u v w B a hB hB30 hcop ha hval

theorem long_no_bounded_length {B H : ℕ} (hB : 0 < B)
    (_hcop : Nat.Coprime B 30) (_hH : 1 ≤ H) :
    Set.Finite {lo : ℕ | ∃ len : ℕ, 1 ≤ len ∧ len ≤ H ∧
      longPaperCap B (lo + len) <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))} := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperR7.long_no_bounded_length B H hB _hcop _hH

theorem short_window_equivalence :
    Irrational paperSeries235 ↔ ShortPaperEscape := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperR7.short_window_equivalence

end PalomarCorpus.E269.PaperStatementsG
