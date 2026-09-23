/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.BranchCellHorizonExclusions
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.UpperResetBandCertificate
import Solutions.PalomarCorpus.E257_31.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBP

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

theorem weakCapFamily_gap_pos :
    let gap : ℕ := 2;
    0 < gap := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapFamily).gap_pos

theorem weakCapFamily_pulse_le :
    let pulse : (Fin 3) → ℕ := weakCapPulse;
    let pulseCap : ℕ := 3;
    ∀ x, pulse x ≤ pulseCap := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapFamily).pulse_le

theorem weakCapFamily_oldSum_injective :
    let oldSum : (Fin 3) → ℕ := weakCapOldSum;
    Function.Injective oldSum := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapFamily).oldSum_injective

theorem weakCapFamily_separated :
    let oldSum : (Fin 3) → ℕ := weakCapOldSum;
    let gap : ℕ := 2;
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapFamily).separated

theorem weakCapFamily_pulseCap_lt_three_gap :
    let gap : ℕ := 2;
    let pulseCap : ℕ := 3;
    pulseCap < 3 * gap := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapFamily).pulseCap_lt_three_gap

noncomputable def weakCapFamily : PerturbedFamily (Fin 3) where
  oldSum := weakCapOldSum
  pulse := weakCapPulse
  gap := 2
  pulseCap := 3
  gap_pos := @weakCapFamily_gap_pos
  pulse_le := @weakCapFamily_pulse_le
  oldSum_injective := @weakCapFamily_oldSum_injective
  separated := @weakCapFamily_separated
  pulseCap_lt_three_gap := @weakCapFamily_pulseCap_lt_three_gap

theorem weakCapCut_below_admissible :
    let F := weakCapFamily;
    let C := 2;
    let below := 1;
    F.oldSum below ≤ C := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapCut).below_admissible

theorem weakCapCut_below_maximal :
    let F := weakCapFamily;
    let C := 2;
    let below := 1;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapCut).below_maximal

theorem weakCapCut_above_strict :
    let F := weakCapFamily;
    let C := 2;
    let above := 2;
    C < F.oldSum above := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapCut).above_strict

theorem weakCapCut_above_minimal :
    let F := weakCapFamily;
    let C := 2;
    let above := 2;
    ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x := (@ErdosProblems.Erdos257.PaperCompleteR21.weakCapCut).above_minimal

noncomputable def weakCapCut : weakCapFamily.AdjacentCut 2 where
  below := 1
  above := 2
  below_admissible := @weakCapCut_below_admissible
  below_maximal := @weakCapCut_below_maximal
  above_strict := @weakCapCut_above_strict
  above_minimal := @weakCapCut_above_minimal

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

theorem paper_perturbed_separation_global_maximality {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice := by
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_separation_global_maximality α (PerturbedFamily_transport_toSrc F) C (PerturbedFamily.AdjacentCut_transport_toSrc K) (inferInstanceAs (Decidable K.successorCarries)) hsep x hx

theorem paper_perturbed_two_stage_is_global_maximum {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) := by
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_two_stage_is_global_maximum α (PerturbedFamily_transport_toSrc F) C (PerturbedFamily.AdjacentCut_transport_toSrc K) (inferInstanceAs (Decidable K.successorCarries)) hcap hsep

theorem paper_perturbed_weak_cap_counterexample :
    ¬ weakCapFamily.pulseCap < weakCapFamily.gap ∧
      weakCapFamily.pulseCap < 3 * weakCapFamily.gap ∧
      ¬ weakCapCut.successorCarries ∧
      weakCapCut.newCapacity = 10 ∧
      weakCapFamily.newSum weakCapCut.below = 11 ∧
      ¬ weakCapFamily.newSum weakCapCut.below ≤ weakCapCut.newCapacity ∧
      weakCapFamily.newSum (0 : Fin 3) ≤ weakCapCut.newCapacity := @ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_weak_cap_counterexample

theorem paper_successor_remainders_fourteen_through_thirtyone :
    seamIntegerGreedyRemainder 14 = 392 ∧
      seamIntegerGreedyRemainder 15 = 34333 ∧
      seamIntegerGreedyRemainder 16 = 71791 ∧
      seamIntegerGreedyRemainder 17 = 156085 ∧
      seamIntegerGreedyRemainder 18 = 362187 ∧
      seamIntegerGreedyRemainder 19 = 924455 ∧
      seamIntegerGreedyRemainder 20 = 549353 ∧
      seamIntegerGreedyRemainder 21 = 100251 ∧
      seamIntegerGreedyRemainder 22 = 4595307 ∧
      seamIntegerGreedyRemainder 23 = 9992613 ∧
      seamIntegerGreedyRemainder 24 = 23193229 ∧
      seamIntegerGreedyRemainder 25 = 59218477 ∧
      seamIntegerGreedyRemainder 26 = 35546625 ∧
      seamIntegerGreedyRemainder 27 = 7968765 ∧
      seamIntegerGreedyRemainder 28 = 300310513 ∧
      seamIntegerGreedyRemainder 29 = 664371133 ∧
      seamIntegerGreedyRemainder 30 = 1583742700 ∧
      seamIntegerGreedyRemainder 31 = 4187487147 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_successor_remainders_fourteen_through_thirtyone

theorem paper_unsafe_middle_range_is_three_integers {s : ℕ} (hs : 5 ≤ s) :
    ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) ↔
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -3 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -2 ∨
          4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -1 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_unsafe_middle_range_is_three_integers s hs

theorem paper_upper_branch_needs_no_exceptional_cell {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∧
      0 ≤ 4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse ∧
      seamIntegerGreedyRemainder (s + 1) +
          (4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse) =
        2 ^ (s + 1) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_upper_branch_needs_no_exceptional_cell s hs hcarry

end PalomarCorpus.E257.PaperStructuresBP
