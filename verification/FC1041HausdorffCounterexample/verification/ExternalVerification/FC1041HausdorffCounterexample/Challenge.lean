/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent statement-only Challenge for the Hausdorff-length formulation
of Formal Conjectures Erdős1041. The hole is a trusted comparison target.
`fcLength` copies the original source definition exactly. -/

noncomputable section
open scoped ENNReal
open MeasureTheory Polynomial Metric

namespace Erdos1041.Counterexample

noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by sorry

end Erdos1041.Counterexample
