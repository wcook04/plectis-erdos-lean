/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band b

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Set

namespace PalomarCorpus.E1041.PaperStatementsAB
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Set
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.weightedProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedProduct {m : ℕ} (c : Fin m → ℂ) (w : Fin m → ℝ) (z : ℂ) : ℝ :=
  ∏ k, ‖1 - conj (c k) * z‖ ^ w k
/-- Includes the displayed equality classification; proving the inequality alone is not counted as proving this target. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.WeightedFreePoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)
/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.paper_weighted_free_point in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_weighted_free_point : WeightedFreePoint := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAB
