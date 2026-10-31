/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, note sections 2 to 8: proof under a lower bound on the error; the arithmetic ingredients; a criterion using new maxima of an LCM numerator

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
open scoped Topology
open MeasureTheory

namespace PalomarCorpus.E243.PaperStatementsA
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. Local copy of ErdosProblems.Erdos243.nextDenState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. Local copy of ErdosProblems.Erdos243.nextTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- The next denominator defect from the Sylvester step. Local copy of ErdosProblems.Erdos243.sylvesterDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a
/-- States res:absorb, res:descent from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.absorption_and_descent in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem absorption_and_descent :
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      (∀ n, Int.natAbs (E n) < C n) →
      ∀ n, E n = 0 → E (n + 1) = 0) ∧
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      (∃ N, ∀ n, N ≤ n → 0 ≤ E n) →
      ∃ N, ∀ n, N ≤ n → E n = 0) := by
  sorry
/-- States res:cor from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.bounded_negative_endpoint_eventual_multiplier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_negative_endpoint_eventual_multiplier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States res:defect, res:update from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.error_identities in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem error_identities (a aNext D C : ℤ) :
    nextTailState a D C = C - centeredState a D C ∧
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  sorry
/-- States res:eventual, res:step from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.natural_sylvester_of_eventual_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem natural_sylvester_of_eventual_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hzero : ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States res:crt from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.exists_shifted_consecutiveMultiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_shifted_consecutiveMultiples
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ x, L < x ∧ ∀ i : Fin k, m i ∣ x + i.1 := by
  sorry
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsS
open Filter
/-- Cumulative least common multiple of the initial denominator and all digits strictly before `n`. Local copy of ErdosProblems.Erdos243.cumulativeDigitLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.lcmDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- States res:lcmbounded from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_lcm_bounded_defect in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem original_coordinate_lcm_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → lcmDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
end PalomarCorpus.E243.PaperStatementsS

namespace PalomarCorpus.E243.PaperStatementsJ
open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
open scoped Topology
open MeasureTheory
/-- For a nonnegative locally integrable function this is the usual statement that the improper integral from one to infinity is +∞. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.realCutoffPrefixMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realCutoffPrefixMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if (u j : ℝ) ≤ X then w j else 0
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.RealPrefixLowerDensityZero, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealPrefixLowerDensityZero (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  Filter.liminf (fun X : ℝ => realCutoffPrefixMass u w X / ENNReal.ofReal X) atTop = 0
/-- States res:weights from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.real_lowerDensityZero_iff_exists_admissible_real_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsJ
