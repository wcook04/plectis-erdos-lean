/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.Counterexample.HausdorffLength
import Solutions.PalomarCorpus.E1041_01.Statement

open scoped ENNReal
open MeasureTheory Polynomial Metric

/- Copyright (c) 2026 Will Cook. Released under Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsAE

theorem erdos1041_counterexample_hausdorff :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K →
          K ⊆ {z : ℂ | ‖p.eval z‖ < 1} → (2 : ℝ≥0∞) < μH[1] K := by
  rcases Erdos1041.Counterexample.erdos1041_counterexample with
    ⟨hmonic, hdegree, hroots, hnodup, _⟩
  refine ⟨Erdos1041.Counterexample.f, hmonic, hdegree, hroots, hnodup, ?_⟩
  intro z₁ z₂ hr₁ hr₂ hne K hK hz₁ hz₂ hsub
  exact Erdos1041.Counterexample.erdos1041_counterexample_hausdorff
    z₁ z₂ hr₁ hr₂ hne K hK hz₁ hz₂ hsub

theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧ fcLength (Set.range γ) < 2 :=
  @Erdos1041.Counterexample.erdos1041_hausdorff_negation

theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧ fcLength (Set.range γ) < 2 :=
  @Erdos1041.Counterexample.erdos1041_hausdorff_answer_false

end PalomarCorpus.E1041.PaperStatementsAE
