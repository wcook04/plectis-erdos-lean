/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperNoDecayR9
import Solutions.PalomarCorpus.E1049.Statement

open Filter Asymptotics
open scoped Topology

namespace PalomarCorpus.E1049.ArchimedeanCap

theorem archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (max (height (U n)) (height (V n))) ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ width U V n * remainder U V F ((a : ℝ) / b) n)
        atTop (𝓝 0) := by
  exact ErdosProblems.Erdos1049.PaperR9.short_note_archimedean_cap U V F σ δ h
    ⟨hσ, hδ, hh, hdeg, hheight, hne, hrate⟩

/-- Exact all-base hypotheses; no limit of the normalized degree is assumed. -/
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log ((max (maxCoefficient (U n)) (maxCoefficient (V n)) : ℕ) : ℝ)
        ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ width U V n *
      remainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  exact ErdosProblems.Erdos1049.PaperR9.cleared_below_square_not_tendsto_zero
    U V F σ δ h ⟨hσ, hδ, hh, hdeg, hheight, hne, hrate⟩ a b hb hab hsquare

end PalomarCorpus.E1049.ArchimedeanCap
