/- Copyright (c) 2026 Will Cook. Released under Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Polynomial Metric

namespace Erdos249257.ExternalVerification1041PaperStatementsAE

noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_counterexample_hausdorff in the substantive development. Ani constructed the polynomial; the theorem quantifies a preconnected root-joining set. -/
theorem erdos1041_counterexample_hausdorff :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K →
          K ⊆ {z : ℂ | ‖p.eval z‖ < 1} → (2 : ℝ≥0∞) < μH[1] K := by
  sorry

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_hausdorff_negation in the substantive development; length is the Hausdorff measure of the path image. -/
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧ fcLength (Set.range γ) < 2 := by
  sorry

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_hausdorff_answer_false in the substantive development; answer(False) uses path-image Hausdorff measure. -/
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧ fcLength (Set.range γ) < 2 := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsAE
