/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperAsymptoticsR9
import ErdosProblems.Erdos1049.PaperLongCapR9
import ErdosProblems.Erdos1049.PaperShortCapR9
import Solutions.PalomarCorpus.E1049d.Statement

open Filter
open Asymptotics
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresD

/-- The copied predicate bundle `LongCapHypotheses` and its source `ErdosProblems.Erdos1049.PaperR9.LongCapHypotheses` have the
same fields, so they are the same proposition. This equivalence is the fidelity
evidence for every statement below that mentions it. -/
theorem LongCapHypotheses_transport_bridge {U V : ℕ → Polynomial ℤ} {F : ℝ → ℝ} {σ δ h : ℝ} :
    LongCapHypotheses U V F σ δ h ↔ ErdosProblems.Erdos1049.PaperR9.LongCapHypotheses U V F σ δ h := by
  first
  | (exact ⟨fun hx => ⟨hx.sigma_pos, hx.delta_pos, hx.height_nonneg, hx.degree_upper, hx.height_upper, hx.nonzero, hx.remainder_rate⟩, fun hx => ⟨hx.sigma_pos, hx.delta_pos, hx.height_nonneg, hx.degree_upper, hx.height_upper, hx.nonzero, hx.remainder_rate⟩⟩; done)
  | (constructor <;> (intro hx; constructor <;> simp_all); done)

theorem long_record_archcap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h) :
    σ ≤ δ ∧ σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Filter.limsup (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop ≤
        δ * Real.log b - σ * Real.log ((a : ℝ) / b)) ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
        Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
    (∀ d : ℝ,
      Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d) →
        σ ≤ d ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          Tendsto (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
            polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop
            (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b)))) ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          (Real.log b / Real.log a < σ / (σ + d) →
            Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
          (σ / (σ + d) < Real.log b / Real.log a →
            Tendsto (fun n => |(b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n|) atTop atTop)) ∧
        Tendsto (fun n => |(2 : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((3 : ℝ) / 2) n|) atTop atTop) := @ErdosProblems.Erdos1049.PaperR9.long_record_archcap U V F σ δ h (LongCapHypotheses_transport_bridge.mp H)

end PalomarCorpus.E1049.PaperStructuresD
