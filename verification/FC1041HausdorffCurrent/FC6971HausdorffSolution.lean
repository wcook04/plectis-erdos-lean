import ErdosProblems.Erdos1041.Counterexample.HausdorffLength

open Polynomial MeasureTheory ENNReal

namespace Erdos1041

noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

set_option linter.unusedVariables false in
theorem erdos_1041 :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ length (Set.range γ) < 2 := by
  exact Erdos1041.Counterexample.erdos1041_hausdorff_answer_false

end Erdos1041

#print axioms Erdos1041.erdos_1041
