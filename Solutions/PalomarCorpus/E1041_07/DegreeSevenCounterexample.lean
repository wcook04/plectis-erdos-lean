/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.Counterexample.CatalogueAdapter
import Solutions.PalomarCorpus.E1041_07.Statement

open scoped ENNReal
open Polynomial Metric

set_option autoImplicit false

noncomputable section

namespace PalomarCorpus.E1041.DegreeSevenCounterexample

/-- Ani's explicit degree-seven example disproves the stated total-variation formulation
associated with Erdős problem 1041: every strict-lemniscate path between distinct roots has total
variation greater than `2`. -/
theorem degreeSevenCounterexample :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
          γ 0 = z₁ → γ 1 = z₂ →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) →
          (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
  exact Erdos1041.Counterexample.erdos1041_ani_degree_seven

end PalomarCorpus.E1041.DegreeSevenCounterexample

#print axioms PalomarCorpus.E1041.DegreeSevenCounterexample.degreeSevenCounterexample
