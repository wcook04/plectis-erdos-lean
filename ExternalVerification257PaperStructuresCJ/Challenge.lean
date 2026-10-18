/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.HalfCylinderIntegerGreedy`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresCJ

structure PerturbedFamily (α : Type*) where
  oldSum : α → ℕ
  pulse : α → ℕ
  gap : ℕ
  pulseCap : ℕ
  gap_pos : 0 < gap
  pulse_le : ∀ x, pulse x ≤ pulseCap
  oldSum_injective : Function.Injective oldSum
  separated : ∀ {x y}, oldSum x < oldSum y →
    oldSum x + gap ≤ oldSum y
  pulseCap_lt_three_gap : pulseCap < 3 * gap

structure PerturbedFamily.AdjacentCut {α : Type*} (F : PerturbedFamily α) (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x

noncomputable def PerturbedFamily.AdjacentCut.abovePulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.above

noncomputable def PerturbedFamily.AdjacentCut.belowPulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.below

noncomputable def PerturbedFamily.AdjacentCut.newCapacity {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 4 * C + F.gap

noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C

noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below

noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap

noncomputable def PerturbedFamily.AdjacentCut.prefixRemainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : ℕ :=
  if K.successorCarries then
    F.gap - (4 * K.overshoot + K.abovePulse)
  else
    4 * K.remainder + F.gap - K.belowPulse

noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4

noncomputable def PerturbedFamily.AdjacentCut.nextRemainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : ℕ :=
  if K.terminalWeight ≤ K.prefixRemainder then
    K.prefixRemainder - K.terminalWeight
  else
    K.prefixRemainder

noncomputable def PerturbedFamily.AdjacentCut.prefixChoice {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : α :=
  if K.successorCarries then K.above else K.below

noncomputable def PerturbedFamily.newSum {α : Type*} (F : PerturbedFamily α) (x : α) : ℕ := 4 * F.oldSum x + F.pulse x

/-- States thm:perturbed-family-maximality from the long record for Erdős problem #257.
Transported from
Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.above_newSum_le_capacity_iff
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem above_newSum_le_capacity_iff {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) :
    F.newSum K.above ≤ K.newCapacity ↔ K.successorCarries := by
  sorry

/-- States thm:perturbed-family-maximality from the long record for Erdős problem #257.
Transported from
Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.below_newSum_le_capacity
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem below_newSum_le_capacity {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    (hcap : F.pulseCap < F.gap) :
    F.newSum K.below ≤ K.newCapacity := by
  sorry

/-- States thm:perturbed-family-maximality from the long record for Erdős problem #257.
Transported from
Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem nextRemainder_trichotomy {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    [Decidable K.successorCarries] :
    K.nextRemainder =
      if K.successorCarries then
        F.gap - (4 * K.overshoot + K.abovePulse)
      else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
        4 * K.remainder + F.gap - K.belowPulse
      else
        4 * K.remainder - F.gap - K.belowPulse - 4 := by
  sorry

/-- States thm:perturbed-family-maximality from the long record for Erdős problem #257.
Transported from
Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixChoice_maximal in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem prefixChoice_maximal {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    (hcap : F.pulseCap < F.gap)
    [Decidable K.successorCarries]
    {x : α} (hx : F.newSum x ≤ K.newCapacity) :
    F.newSum x ≤ F.newSum K.prefixChoice := by
  sorry

/-- States thm:perturbed-family-maximality from the long record for Erdős problem #257.
Transported from
Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixRemainder_eq_capacity_sub_choice
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem prefixRemainder_eq_capacity_sub_choice {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    [Decidable K.successorCarries] :
    K.prefixRemainder = K.newCapacity - F.newSum K.prefixChoice := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCJ
