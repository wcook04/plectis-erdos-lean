/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record sections 7 to 9: new maxima of reduced numerators; descent when the error is nonnegative; when the negative error is constant

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243_07.Shared
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The denominator q multiplied by the product of the first n terms of a. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The canonical centred error `E_n = D_n - (a_n - 1) C_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.canonicalError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalError (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℤ)
/-- The correction term `Λ_n` of `long243:eq:shiftedsign`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext
/-- `Λ_n` on the canonical orbit. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCorrection (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℝ :=
  shiftedCorrectionTerm (a n : ℝ) (a (n + 1) : ℝ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
    ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)
    ((canonicalError a p q n : ℤ) : ℝ) ((canonicalError a p q (n + 1) : ℤ) : ℝ)
end PalomarCorpus.E243_07.Shared

namespace PalomarCorpus.E243.PaperStatementsE
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (shiftedCorrectionTerm)
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_shiftedCorrection in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem growthDefect_eq_neg_relativeError_add_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedCorrectionTerm a aNext C CNext E ENext := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm_pos_and_lt_three_div in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shiftedCorrectionTerm_pos_and_lt_three_div
    {A ANext C CNext E ENext : ℝ}
    (hA : 2 ≤ A) (hANext : A ^ 2 / 2 ≤ ANext)
    (hθ : |E / C| ≤ 1 / 4) (hθNext : |ENext / CNext| ≤ 1 / 4) :
    0 < shiftedCorrectionTerm A ANext C CNext E ENext ∧
      shiftedCorrectionTerm A ANext C CNext E ENext < 3 / A := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sylvesterTail_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (ha : 1 < a)
    (hsyl : aNext = a ^ 2 - a + 1)
    (hzero : E = 0) :
    ENext = 0 ∧
      shiftedCorrectionTerm a aNext C CNext E ENext = (a - 1) / aNext ∧
      0 < shiftedCorrectionTerm a aNext C CNext E ENext := by
  sorry
end PalomarCorpus.E243.PaperStatementsE

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (canonicalCorrection canonicalDenominator canonicalError canonicalNaturalNumerator centeredState clearedIntegerNumerator prefixProduct shiftedCorrectionTerm)
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection_pos_and_lt_three_div in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonicalCorrection_pos_and_lt_three_div
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      0 < canonicalCorrection a p q n ∧
        canonicalCorrection a p q n < 3 / (a n : ℝ) := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.canonical_growthDefect_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_growthDefect_identity
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 =
      -(((canonicalError a p q n : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)) +
        canonicalCorrection a p q n := by
  sorry
end PalomarCorpus.E243.PaperStatementsL

namespace PalomarCorpus.E243.PaperStatementsQ
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (canonicalCorrection canonicalDenominator canonicalError canonicalNaturalNumerator centeredState clearedIntegerNumerator prefixProduct shiftedCorrectionTerm)
/-- Cumulative least common multiple of the initial denominator and all digits strictly before `n`. Local copy of ErdosProblems.Erdos243.cumulativeDigitLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- The Erdős-Straus quantity `Z_n^ES = ([a_0,…,a_n]/a_{n+1})(a_{n+1}²/a_{n+2} - 1)`. The least common multiple is the `q = 1` cumulative one: it includes `a_n` and not the clearing denominator. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosStrausQuantity (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a (n + 1) : ℝ) / (a (n + 1) : ℝ) *
    ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1)
/-- The LCM-cleared numerator `U_n = L_n x_n`. It is an integer because `q ∣ L_n` and `a_j ∣ L_n` for every `j < n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.lcmClearedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmClearedNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * ((cumulativeDigitLcm q a n / q : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, ((cumulativeDigitLcm q a n / a j : ℕ) : ℤ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.productDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- Cumulative product of the irreversible LCM-overlap payments. Local copy of ErdosProblems.Erdos243.cumulativeOverlapDebt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)
/-- Product-cleared denominator scale through the first `n` digits. Local copy of ErdosProblems.Erdos243.digitProductScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digitProductScale (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * digitProductScale q a n
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.canonicalError_div_overlapDebt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.digitProductScale_eq_canonicalDenominator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem digitProductScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_ne_productDefect_ne_lcmShift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdosStrausQuantity_ne_productDefect_ne_lcmShift :
    ∃ (a : ℕ → ℕ) (q n : ℕ), 0 < q ∧ (∀ m, 0 < a m) ∧
      erdosStrausQuantity a n ≠ productDefect a n ∧
      erdosStrausQuantity a n ≠
        (cumulativeDigitLcm q a n : ℝ) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1) / (a (n + 1) : ℝ) := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_sign in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.erdosStraus_lcm_includes_digit_not_denominator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdosStraus_lcm_includes_digit_not_denominator (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm 1 a (n + 1) = Nat.lcm (cumulativeDigitLcm 1 a n) (a n) ∧
      a n ∣ cumulativeDigitLcm 1 a (n + 1) ∧
      cumulativeDigitLcm 1 a 0 = 1 := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlapDebt_dvd_gcd
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < cumulativeOverlapDebt q a n ∧
      cumulativeOverlapDebt q a n *  cumulativeDigitLcm q a n =
        canonicalDenominator a q n ∧
      cumulativeOverlapDebt q a n ∣
        Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_mul_lcmClearedNumerator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlapDebt_mul_lcmClearedNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * lcmClearedNumerator a p q n =
      clearedIntegerNumerator a p q n := by
  sorry
end PalomarCorpus.E243.PaperStatementsQ

namespace PalomarCorpus.E243.PaperStatementsD
open Filter
open scoped BigOperators
open scoped Topology
/-- `ℓ x = log₂ log₂ max(4, x)`, the scale of the long #243 note. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.ellScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ellScale (x : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (max 4 x))
/-- States long243:res:coprimalitycap from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_avoiding_in_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_avoiding_in_window
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {x L : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hkL : ((({i | m i ≤ x + L} : Set ℕ).ncard : ℝ)) / (1 - θ) < (L : ℝ)) :
    ∃ n, x ≤ n ∧ n < x + L ∧ ∀ i, ¬ m i ∣ n := by
  sorry
/-- States long243:res:coprimalitycap from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_slow_rise_avoiding_sequence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_slow_rise_avoiding_sequence
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    (hscale : ∃ C : ℝ, ∀ i, |ellScale (m i : ℝ) - (i : ℝ)| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℕ) (u : ℕ → ℕ), StrictMono u ∧ (∀ n, 0 < u n) ∧
      (∀ i, T ≤ i → ∀ n, ¬ m i ∣ u n) ∧
      ∀ᶠ n in atTop, ((u (n + 1) : ℝ) - (u n : ℝ)) ≤ (1 + ε) * ellScale (u n : ℝ) := by
  sorry
end PalomarCorpus.E243.PaperStatementsD

namespace PalomarCorpus.E243.PaperStatementsA
/-- States long243:res:constant from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_constantNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_constantNegative_shapeEquation
    (m c : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D n + m = (a n - 1) * (c + n * m)) := by
  sorry
/-- States long243:res:constant from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_eventuallyConstantNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_eventuallyConstantNegative_shapeEquation
    (m c N : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D (N + n) + m = (a (N + n) - 1) * (c + n * m)) := by
  sorry
/-- States long243:res:descent from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.centeredState_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  sorry
end PalomarCorpus.E243.PaperStatementsA
