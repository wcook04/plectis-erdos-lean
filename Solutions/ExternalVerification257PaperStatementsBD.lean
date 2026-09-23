/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import ErdosProblems.Erdos257.PaperCompleteR21.BalancedPulseFanOutCount
import ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.HalfCarryReachability`,
`ErdosProblems.Erdos257.PaperCompleteR21.BalancedPulseFanOutCount`,
`ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths`.
-/

open Filter
open Set

namespace Erdos249257.ExternalVerification257PaperStatementsBD

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2

noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0

noncomputable def balancedPulseFamily (m : ℕ) : Set (ℕ → ℕ) :=
  balancedPulseCoeff m '' Set.Iic (balancedPulseRadius m)

theorem balancedPulseCoeff_injective (m : ℕ) :
    Function.Injective (balancedPulseCoeff m) := @ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseCoeff_injective m

theorem four_le_halfStripBound (m : ℕ) : 4 ≤ halfStripBound m := @ErdosProblems.Erdos257.PaperCompleteR21.four_le_halfStripBound m

theorem paper_balanced_pulse_fanout_is_radius_succ (m : ℕ) :
    (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 ∧
      (balancedPulseFamily m).ncard = (m + 1) / 2 + 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ m

theorem paper_balanced_pulse_fanout_unbounded_corrected :
    (∀ m : ℕ, m / 2 + 1 ≤ (balancedPulseFamily m).ncard) ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ (balancedPulseFamily m).ncard := @ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_unbounded_corrected

theorem paper_pulse_family_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card m State inferInstance state decode hdecode

theorem paper_pulse_family_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := @ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_no_autonomous_decoder State m hm state hstate

end Erdos249257.ExternalVerification257PaperStatementsBD
