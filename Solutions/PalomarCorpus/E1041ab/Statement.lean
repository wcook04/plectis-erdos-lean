/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041ab

Every non-theorem declaration of `PalomarCorpus/E1041ab/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1041.PaperStatementsAB
