import Mathlib

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open Polynomial Metric MeasureTheory

namespace Erdos249257.ExternalVerification1041HausdorffCounterexample

/-- One degree-seven polynomial has the strict preconnected-set obstruction
asserted in the short and long Erdős 1041 papers. -/
theorem preconnected_hausdorff_counterexample :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K →
          K ⊆ {z : ℂ | ‖p.eval z‖ < 1} →
          (2 : ℝ≥0∞) < μH[1] K := by
  sorry

end Erdos249257.ExternalVerification1041HausdorffCounterexample
