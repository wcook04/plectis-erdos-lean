/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets`,
`ErdosProblems.Erdos257.PaperCompleteR7.PrimeWeightedDefinitions`,
`ErdosProblems.Erdos257.PaperCompleteR8.OldCoverObstruction`,
`ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresCI

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d

noncomputable def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)

noncomputable def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))

noncomputable def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}

noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable

noncomputable def PositiveCoverData.oldCostTerm (C : PositiveCoverData) (j : ℕ) : ℝ :=
  C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) *
    (2 : ℝ) ^ C.exponent j / (((2 : ℝ) ^ C.exponent j - 1) ^ 2)

noncomputable def PositiveCoverData.OldCostSummable (C : PositiveCoverData) : Prop :=
  Summable C.oldCostTerm

noncomputable def HasOldPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.OldCostSummable

/-- States res:weighted-cover-incomparability from the short record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR8.exists_strengthened_not_old_or_weighted_host in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_strengthened_not_old_or_weighted_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A ∧
      (¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCI
