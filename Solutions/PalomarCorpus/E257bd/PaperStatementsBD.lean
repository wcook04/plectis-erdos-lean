/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import ErdosProblems.Erdos257.PaperCompleteR21.BalancedPulseFanOutCount
import ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths
import Solutions.PalomarCorpus.E257bd.Statement

open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsBD

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

end PalomarCorpus.E257.PaperStatementsBD
