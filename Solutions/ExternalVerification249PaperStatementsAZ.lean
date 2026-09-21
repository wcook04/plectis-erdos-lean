/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GenericTailOrbitRigidity
import ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`,
`ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss`.
-/

open Filter
open Set

namespace Erdos249257.ExternalVerification249PaperStatementsAZ

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2

noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := @ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset a u0 v0 L

theorem balancedPulse_common_history (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    (∀ n : ℕ, n ≠ m → n ≠ m + 1 → balancedPulseCoeff m r n = 0)
      ∧ balancedPulseCoeff m r m = balancedPulseRadius m - r
      ∧ balancedPulseCoeff m r (m + 1) = 2 * r
      ∧ (∀ n : ℕ, balancedPulseCoeff m r n ≤ n)
      ∧ binaryCoeffSeries (balancedPulseCoeff m r)
          = (balancedPulseRadius m : ℝ) / 2 ^ m
      ∧ (∀ N : ℕ, N < m → binaryCoeffTail (balancedPulseCoeff m r) N
          = (balancedPulseRadius m : ℝ) / 2 ^ (m - N))
      ∧ binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_common_history m hm r hr

theorem balancedPulse_label_lower_bound {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ) (decode : Λ → ℕ)
    (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_label_lower_bound <;> assumption

theorem balancedPulse_no_decoder_from_common_state
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := @ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_no_decoder_from_common_state State m hm state hstate

theorem balancedPulse_series (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffSeries (balancedPulseCoeff m r)
      = (balancedPulseRadius m : ℝ) / 2 ^ m := @ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_series m hm r hr

theorem balancedPulse_tail_at (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_tail_at m r hm hr

end Erdos249257.ExternalVerification249PaperStatementsAZ
