import Mathlib
import ErdosProblems.Erdos1041.Counterexample.HausdorffLength

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open Polynomial Metric MeasureTheory

namespace Erdos249257.ExternalVerification1041HausdorffCounterexample

theorem preconnected_hausdorff_counterexample :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K →
          K ⊆ {z : ℂ | ‖p.eval z‖ < 1} →
          (2 : ℝ≥0∞) < μH[1] K := by
  rcases Erdos1041.Counterexample.erdos1041_counterexample with
    ⟨hmonic, hdegree, hdisc, hnodup, _⟩
  refine ⟨Erdos1041.Counterexample.f, hmonic, hdegree, hdisc, hnodup, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hne K hK hz₁K hz₂K hsubset
  change K ⊆ Erdos1041.Counterexample.Omega Erdos1041.Counterexample.f at hsubset
  exact Erdos1041.Counterexample.erdos1041_counterexample_hausdorff
    z₁ z₂ hz₁ hz₂ hne K hK hz₁K hz₂K hsubset

end Erdos249257.ExternalVerification1041HausdorffCounterexample

#print axioms Erdos249257.ExternalVerification1041HausdorffCounterexample.preconnected_hausdorff_counterexample
