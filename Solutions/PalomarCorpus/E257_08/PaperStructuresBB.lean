/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFloorErrorReset
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderLargestSkipGap
import Erdos249257.HalfCylinderLargestSkipInduction
import Erdos249257.HalfCylinderMiddleCarryLowerBound
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies
import ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit
import Solutions.PalomarCorpus.E257_08.Statement

open Set
open Filter
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBB

/-- The copied structure `PerturbedFamily` and its source `Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily` carry the same
fields, so each converts into the other field by field. -/
noncomputable def PerturbedFamily_transport_toSrc {α : Type*} (x : PerturbedFamily α) :
    Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α :=
  ⟨x.oldSum, x.pulse, x.gap, x.pulseCap, x.gap_pos, x.pulse_le, x.oldSum_injective, x.separated, x.pulseCap_lt_three_gap⟩

/-- The inverse of `PerturbedFamily_transport_toSrc`. -/
noncomputable def PerturbedFamily_transport_ofSrc {α : Type*} (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    PerturbedFamily α :=
  ⟨x.oldSum, x.pulse, x.gap, x.pulseCap, x.gap_pos, x.pulse_le, x.oldSum_injective, x.separated, x.pulseCap_lt_three_gap⟩

@[simp] theorem PerturbedFamily_transport_toSrc_oldSum {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).oldSum = x.oldSum := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_oldSum {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).oldSum = x.oldSum := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_pulse {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).pulse = x.pulse := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_pulse {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).pulse = x.pulse := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_gap {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).gap = x.gap := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_gap {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).gap = x.gap := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_pulseCap {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).pulseCap = x.pulseCap := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_pulseCap {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).pulseCap = x.pulseCap := rfl

/-- The copied structure `PerturbedFamily.AdjacentCut` and its source `Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut` carry the same
fields, so each converts into the other field by field. -/
noncomputable def PerturbedFamily.AdjacentCut_transport_toSrc {α : Type*} {F : PerturbedFamily α} {C : ℕ} (x : @PerturbedFamily.AdjacentCut α F C) :
    @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut α (PerturbedFamily_transport_toSrc F) C :=
  ⟨x.below, x.above, x.below_admissible, x.below_maximal, x.above_strict, x.above_minimal⟩

/-- The inverse of `PerturbedFamily.AdjacentCut_transport_toSrc`. -/
noncomputable def PerturbedFamily.AdjacentCut_transport_ofSrc {α : Type*} {F : PerturbedFamily α} {C : ℕ} (x : @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut α (PerturbedFamily_transport_toSrc F) C) :
    @PerturbedFamily.AdjacentCut α F C :=
  ⟨x.below, x.above, x.below_admissible, x.below_maximal, x.above_strict, x.above_minimal⟩

theorem SeamTwoSidedDyadicCellEscape.twoSided
    (hescape : SeamTwoSidedDyadicCellEscape)
    (s : ℕ) (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
      (seamAdjacentCut s hs).overshoot ≤ 2 ^ s := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided hescape s hs

theorem largestSkipLateAt_fourteen : LargestSkipLateAt 14 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.largestSkipLateAt_fourteen

theorem seamUpperBranch_remainder_add_resetCharge_eq
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamIntegerGreedyRemainder (d + 1) +
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) =
      2 ^ (d + 1) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq d hd5 hcarry

theorem mem_seamGreedySupport_iff_scaled {s d : ℕ} (hs : 2 ≤ s) (h2 : 2 ≤ d)
    (hd : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s)
      ↔ seamScaledWeight s d
          ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) (d - 2) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.mem_seamGreedySupport_iff_scaled s d hs h2 hd

theorem paperResetSqrtEscape_iff_square :
    PaperResetSqrtEscape ↔ SeamResetSqrtEscape := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paperResetSqrtEscape_iff_square

end PalomarCorpus.E257.PaperStructuresBB
