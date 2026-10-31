/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.PaperAsymptoticsR9
import ErdosProblems.Erdos1049.PaperHomogenisationR7
import ErdosProblems.Erdos1049.PaperShortCapR9

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperAsymptoticsR9`,
`ErdosProblems.Erdos1049.PaperHomogenisationR7`, `ErdosProblems.Erdos1049.PaperShortCapR9`.
-/

open Filter
open Asymptotics
open scoped Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStructuresR

noncomputable def coeffL1 (P : Polynomial ℤ) : ℝ :=
  ∑ i ∈ P.support, |(P.coeff i : ℝ)|

noncomputable def pairWidth (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ :=
  max (U n).natDegree (V n).natDegree

noncomputable def polynomialRemainder (U V : ℕ → Polynomial ℤ)
    (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x -
    (V n).eval₂ (Int.castRingHom ℝ) x

noncomputable def pairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  max (coeffL1 (U n)) (coeffL1 (V n))

noncomputable def sqScale (n : ℕ) : ℝ := (n : ℝ) ^ 2

noncomputable def QuadUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ (a + ε) * sqScale n

noncomputable def QuadLogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => Real.log |f n| - a * sqScale n) =o[atTop] sqScale

structure CapHypotheses (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  height_nonneg : 0 ≤ h
  degree_upper : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ
  height_upper : QuadUpper (fun n => Real.log (pairHeight U V n)) h
  nonzero : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, polynomialRemainder U V F x n ≠ 0
  remainder_rate : ∀ x : ℝ, 1 < x →
    QuadLogRate (polynomialRemainder U V F x) (-σ * Real.log x)

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

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

end Erdos249257.ExternalVerification1049PaperStructuresR
