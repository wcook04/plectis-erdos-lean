/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderUpperResetBandCertificates
import ErdosProblems.Erdos257.PaperCompleteR21.BranchCellHorizonExclusions
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.UpperResetBandCertificate
import Solutions.PalomarCorpus.E257_12.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBN

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

theorem seamUpperResetDyadicBandEscape_through_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30)
    (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1) := @Erdos249257.seamUpperResetDyadicBandEscape_through_thirty d hd13 hd30 hd5 hcarry

theorem paper_perturbed_nextRemainder_three_branches {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4 := by
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_nextRemainder_three_branches α (PerturbedFamily_transport_toSrc F) C (PerturbedFamily.AdjacentCut_transport_toSrc K) (inferInstanceAs (Decidable K.successorCarries))

theorem paper_perturbed_order_preservation {α : Type*} (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y := by
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_order_preservation α (PerturbedFamily_transport_toSrc F) x y hxy

theorem paper_perturbed_prefixChoice_maximal {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice := by
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_prefixChoice_maximal α (PerturbedFamily_transport_toSrc F) C (PerturbedFamily.AdjacentCut_transport_toSrc K) (inferInstanceAs (Decidable K.successorCarries)) hcap

end PalomarCorpus.E257.PaperStructuresBN
