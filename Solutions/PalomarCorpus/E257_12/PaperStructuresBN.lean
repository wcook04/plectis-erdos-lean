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

theorem seamPerturbedFamily_gap_pos (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    0 < gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).gap_pos

theorem seamPerturbedFamily_oldSum_injective (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    Function.Injective oldSum := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).oldSum_injective

theorem seamPerturbedFamily_separated (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    let gap : ℕ := 2 ^ (s + 1);
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).separated

theorem seamPerturbedFamily_pulseCap_lt_three_gap (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    let pulseCap : ℕ := 2 * (s - 2);
    pulseCap < 3 * gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).pulseCap_lt_three_gap

theorem wordPulse_le (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ 2 * (s - 2) := @Erdos249257.HalfCylinderIntegerGreedy.wordPulse_le s b

noncomputable def seamPerturbedFamily (s : ℕ) (hs : 3 ≤ s) :
    PerturbedFamily (SeamRowWord s) where
  oldSum b := wordWeightSum s b.toNatWord
  pulse b := wordPulse s b.toNatWord
  gap := 2 ^ (s + 1)
  pulseCap := 2 * (s - 2)
  gap_pos := @seamPerturbedFamily_gap_pos s hs
  pulse_le b := wordPulse_le s b.toNatWord
  oldSum_injective := @seamPerturbedFamily_oldSum_injective s hs
  separated := @seamPerturbedFamily_separated s hs
  pulseCap_lt_three_gap := @seamPerturbedFamily_pulseCap_lt_three_gap s hs

theorem exists_seamWord_minimal_above
    {s : ℕ} (hs : 5 ≤ s) :
    ∃ a : SeamRowWord s,
      seamSubsetTarget s <
          (seamPerturbedFamily s (by omega)).oldSum a ∧
        ∀ x : SeamRowWord s,
          seamSubsetTarget s <
              (seamPerturbedFamily s (by omega)).oldSum x →
            (seamPerturbedFamily s (by omega)).oldSum a ≤
              (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.exists_seamWord_minimal_above s hs

theorem integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits_length weights C

noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)

theorem seamAboveWord_minimal
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum x) :
    (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) ≤
      (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_minimal s hs x hx

theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict s hs

theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.seamWeights_length_eq s

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

theorem seamAdjacentCut_below_admissible (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    F.oldSum below ≤ C := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_admissible

theorem seamAdjacentCut_below_maximal (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_maximal

noncomputable def seamAdjacentCut (s : ℕ) (hs : 5 ≤ s) :
    (seamPerturbedFamily s (by omega)).AdjacentCut
      (seamSubsetTarget s) where
  below := seamGreedyWord s
  above := seamAboveWord s hs
  below_admissible := @seamAdjacentCut_below_admissible s hs
  below_maximal := @seamAdjacentCut_below_maximal s hs
  above_strict := seamAboveWord_strict hs
  above_minimal := seamAboveWord_minimal hs

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

theorem paper_final_middle_cell_at_least_neg_two
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (seamAdjacentCut D (by omega)).belowPulse + 2 ≤
        4 * (seamAdjacentCut D (by omega)).remainder ∧
      (-2 : ℤ) ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∧
      ∀ c : ℤ, c ≤ -3 →
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ c := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_at_least_neg_two D hD13 hncarry hmiddle hright

theorem paper_final_middle_cell_ne_neg_three
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
        ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ -3 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_ne_neg_three D hD13 hncarry hmiddle hright

theorem paper_final_middle_cell_remaining_cells
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3 ∨
          4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
            4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
                ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1) →
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_cells D hD13 hncarry hmiddle hright

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
