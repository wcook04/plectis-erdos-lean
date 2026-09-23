/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import Solutions.PalomarCorpus.E257_29.Statement

open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAE
export PalomarCorpus.E257_29.Shared (IsTemperedBinaryOrbit binaryCoeffSeries binaryCoeffTail)

noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)

noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2

noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0

theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r := @Erdos249257.balancedPulse_endpoint_fanout m r

theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  apply Erdos249257.balancedPulse_label_card_lower_bound <;> assumption

theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := @Erdos249257.balancedPulse_no_autonomous_decoder State m hm state hstate

theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m := @Erdos249257.balancedPulse_weighted_pair m r hr

theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := @Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit c hgrowth

theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0) := @Erdos249257.binaryCoeffTail_div_pow_tendsto_zero c hgrowth

theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2 := @Erdos249257.binaryCoeffTail_le c hgrowth N

theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N := @Erdos249257.binaryCoeffTail_nonneg c N

theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := @Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit c hgrowth

theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N := @Erdos249257.temperedBinaryOrbit_eq_scaledTail c hgrowth v u horbit

end PalomarCorpus.E257.PaperStatementsAE
