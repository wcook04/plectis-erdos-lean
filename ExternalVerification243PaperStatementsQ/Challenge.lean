/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.GlobalLcmHeight`,
`ErdosProblems.Erdos243.PaperCompleteR21.ClassicalHalfspaceSigns`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter
open scoped BigOperators

namespace Erdos249257.ExternalVerification243PaperStatementsQ

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def canonicalError (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℤ)

noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext

noncomputable def canonicalCorrection (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℝ :=
  shiftedCorrectionTerm (a n : ℝ) (a (n + 1) : ℝ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
    ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)
    ((canonicalError a p q n : ℤ) : ℝ) ((canonicalError a p q (n + 1) : ℤ) : ℝ)

noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)

noncomputable def erdosStrausQuantity (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a (n + 1) : ℝ) / (a (n + 1) : ℝ) *
    ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1)

noncomputable def lcmClearedNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * ((cumulativeDigitLcm q a n / q : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, ((cumulativeDigitLcm q a n / a j : ℕ) : ℤ)

noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

noncomputable def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)

noncomputable def digitProductScale (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * digitProductScale q a n

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.canonicalError_div_overlapDebt in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.digitProductScale_eq_canonicalDenominator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem digitProductScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_ne_productDefect_ne_lcmShift in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem erdosStrausQuantity_ne_productDefect_ne_lcmShift :
    ∃ (a : ℕ → ℕ) (q n : ℕ), 0 < q ∧ (∀ m, 0 < a m) ∧
      erdosStrausQuantity a n ≠ productDefect a n ∧
      erdosStrausQuantity a n ≠
        (cumulativeDigitLcm q a n : ℝ) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1) / (a (n + 1) : ℝ) := by
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_sign in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.erdosStraus_lcm_includes_digit_not_denominator in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem erdosStraus_lcm_includes_digit_not_denominator (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm 1 a (n + 1) = Nat.lcm (cumulativeDigitLcm 1 a n) (a n) ∧
      a n ∣ cumulativeDigitLcm 1 a (n + 1) ∧
      cumulativeDigitLcm 1 a 0 = 1 := by
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem overlapDebt_dvd_gcd
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < cumulativeOverlapDebt q a n ∧
      cumulativeOverlapDebt q a n *  cumulativeDigitLcm q a n =
        canonicalDenominator a q n ∧
      cumulativeOverlapDebt q a n ∣
        Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) := by
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_mul_lcmClearedNumerator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem overlapDebt_mul_lcmClearedNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * lcmClearedNumerator a p q n =
      clearedIntegerNumerator a p q n := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsQ
