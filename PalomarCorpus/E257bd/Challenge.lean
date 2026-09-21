/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band d

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set

namespace PalomarCorpus.E257.PaperStatementsBD
open Filter
open Set
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
/-- The displayed balanced-pulse family at location `m`: the coefficient sequences `balancedPulseCoeff m r` for the admissible parameters `0 ≤ r ≤ balancedPulseRadius m`. These are exactly the parameters for which the pulse is mass preserving and stays in the linear-growth class (`balancedPulseCoeff_le_self`). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseFamily (m : ℕ) : Set (ℕ → ℕ) :=
  balancedPulseCoeff m '' Set.Iic (balancedPulseRadius m)
/-- States prop:finite-state-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseCoeff_injective in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulseCoeff_injective (m : ℕ) :
    Function.Injective (balancedPulseCoeff m) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.four_le_halfStripBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_le_halfStripBound (m : ℕ) : 4 ≤ halfStripBound m := by
  sorry
/-- States prop:finite-state-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_balanced_pulse_fanout_is_radius_succ (m : ℕ) :
    (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 ∧
      (balancedPulseFamily m).ncard = (m + 1) / 2 + 1 := by
  sorry
/-- States prop:finite-state-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_unbounded_corrected in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_balanced_pulse_fanout_unbounded_corrected :
    (∀ m : ℕ, m / 2 + 1 ≤ (balancedPulseFamily m).ncard) ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ (balancedPulseFamily m).ncard := by
  sorry
/-- States prop:finite-state-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_pulse_family_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1 := by
  sorry
/-- States prop:finite-state-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_no_autonomous_decoder in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_pulse_family_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := by
  sorry
end PalomarCorpus.E257.PaperStatementsBD
