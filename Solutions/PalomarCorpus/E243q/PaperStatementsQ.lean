/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.GlobalLcmHeight
import ErdosProblems.Erdos243.PaperCompleteR21.ClassicalHalfspaceSigns
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Solutions.PalomarCorpus.E243q.Statement

open Filter
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsQ

theorem canonicalError_div_overlapDebt
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
        cumulativeOverlapDebt q a n ∧
      ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      ((Nat.gcd (canonicalNaturalNumerator a p q n)
          (canonicalDenominator a q n) : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) =
        ((Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
            cumulativeOverlapDebt q a n : ℕ) : ℤ) *
          (canonicalError a p q n /
            ((Nat.gcd (canonicalNaturalNumerator a p q n)
              (canonicalDenominator a q n) : ℕ) : ℤ)) ∧
      (0 < canonicalError a p q n ↔
        0 < canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ)) ∧
      (canonicalError a p q n < 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) < 0) ∧
      (canonicalError a p q n = 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) = 0) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.canonicalError_div_overlapDebt a hpos p q hq n

theorem digitProductScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.digitProductScale_eq_canonicalDenominator q a n

theorem erdosStrausQuantity_ne_productDefect_ne_lcmShift :
    ∃ (a : ℕ → ℕ) (q n : ℕ), 0 < q ∧ (∀ m, 0 < a m) ∧
      erdosStrausQuantity a n ≠ productDefect a n ∧
      erdosStrausQuantity a n ≠
        (cumulativeDigitLcm q a n : ℝ) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1) / (a (n + 1) : ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_ne_productDefect_ne_lcmShift

theorem erdosStrausQuantity_sign
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      (0 < erdosStrausQuantity a n ↔
        ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) <
          canonicalCorrection a p q (n + 1)) ∧
      (erdosStrausQuantity a n < 0 ↔
        canonicalCorrection a p q (n + 1) <
          ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)) ∧
      (canonicalError a p q (n + 1) ≤ 0 → 0 < erdosStrausQuantity a n) ∧
      (0 < canonicalError a p q (n + 1) →
        (erdosStrausQuantity a n < 0 ↔
          canonicalCorrection a p q (n + 1) <
            ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
              ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_sign a ha hpos p q hq hs hgrowth

theorem erdosStraus_lcm_includes_digit_not_denominator (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm 1 a (n + 1) = Nat.lcm (cumulativeDigitLcm 1 a n) (a n) ∧
      a n ∣ cumulativeDigitLcm 1 a (n + 1) ∧
      cumulativeDigitLcm 1 a 0 = 1 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.erdosStraus_lcm_includes_digit_not_denominator a n

theorem overlapDebt_dvd_gcd
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < cumulativeOverlapDebt q a n ∧
      cumulativeOverlapDebt q a n *  cumulativeDigitLcm q a n =
        canonicalDenominator a q n ∧
      cumulativeOverlapDebt q a n ∣
        Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd a hpos p q hq n

theorem overlapDebt_mul_lcmClearedNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * lcmClearedNumerator a p q n =
      clearedIntegerNumerator a p q n := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_mul_lcmClearedNumerator a hpos p q hq n

end PalomarCorpus.E243.PaperStatementsQ
