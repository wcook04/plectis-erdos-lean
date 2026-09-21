/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperAnalyticTargets`,
`ErdosProblems.Erdos1041.PaperWeightedRefinementsR10`.
-/

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Set

namespace Erdos249257.ExternalVerification1041PaperStatementsAB

noncomputable def weightedProduct {m : ℕ} (c : Fin m → ℂ) (w : Fin m → ℝ) (z : ℂ) : ℝ :=
  ∏ k, ‖1 - conj (c k) * z‖ ^ w k

noncomputable def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)

/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.paper_weighted_free_point in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem paper_weighted_free_point : WeightedFreePoint := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsAB
