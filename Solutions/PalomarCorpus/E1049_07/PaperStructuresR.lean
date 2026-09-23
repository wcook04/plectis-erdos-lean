/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperAsymptoticsR9
import ErdosProblems.Erdos1049.PaperHomogenisationR7
import ErdosProblems.Erdos1049.PaperShortCapR9
import Solutions.PalomarCorpus.E1049_07.Statement

open Filter
open Asymptotics
open scoped Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresR

/-- The copied predicate bundle `CapHypotheses` and its source `ErdosProblems.Erdos1049.PaperR9.CapHypotheses` have the
same fields, so they are the same proposition. This equivalence is the fidelity
evidence for every statement below that mentions it. -/
theorem CapHypotheses_transport_bridge {U V : ℕ → Polynomial ℤ} {F : ℝ → ℝ} {σ δ h : ℝ} :
    CapHypotheses U V F σ δ h ↔ ErdosProblems.Erdos1049.PaperR9.CapHypotheses U V F σ δ h := by
  first
  | (exact ⟨fun hx => ⟨hx.sigma_pos, hx.delta_pos, hx.height_nonneg, hx.degree_upper, hx.height_upper, hx.nonzero, hx.remainder_rate⟩, fun hx => ⟨hx.sigma_pos, hx.delta_pos, hx.height_nonneg, hx.degree_upper, hx.height_upper, hx.nonzero, hx.remainder_rate⟩⟩; done)
  | (constructor <;> (intro hx; constructor <;> simp_all); done)

theorem short_note_archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := @ErdosProblems.Erdos1049.PaperR9.short_note_archimedean_cap U V F σ δ h (CapHypotheses_transport_bridge.mp H)

end PalomarCorpus.E1049.PaperStructuresR
