/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGlobalRepair
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFloorErrorReset
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderLargestSkipGap
import ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily
import ErdosProblems.Erdos257.PaperCompleteR21.SeamRowGapAndCarry
import Solutions.PalomarCorpus.E257_19.Statement

open Filter
open Set
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBH

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

noncomputable def SeamGreedyUpperOrMiddleAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries ∨
    (¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight)

/-- The copied structure `BooleanMobiusGlobalRepairTrajectory` and its source `Erdos249257.BooleanMobiusGlobalRepairTrajectory` carry the same
fields, so each converts into the other field by field. -/
noncomputable def BooleanMobiusGlobalRepairTrajectory_transport_toSrc (x : BooleanMobiusGlobalRepairTrajectory) :
    Erdos249257.BooleanMobiusGlobalRepairTrajectory :=
  ⟨x.bit, x.frozen_step⟩

/-- The inverse of `BooleanMobiusGlobalRepairTrajectory_transport_toSrc`. -/
noncomputable def BooleanMobiusGlobalRepairTrajectory_transport_ofSrc (x : Erdos249257.BooleanMobiusGlobalRepairTrajectory) :
    BooleanMobiusGlobalRepairTrajectory :=
  ⟨x.bit, x.frozen_step⟩

@[simp] theorem BooleanMobiusGlobalRepairTrajectory_transport_toSrc_bit
    (x : BooleanMobiusGlobalRepairTrajectory) :
    (BooleanMobiusGlobalRepairTrajectory_transport_toSrc x).bit = x.bit := rfl

@[simp] theorem BooleanMobiusGlobalRepairTrajectory_transport_ofSrc_bit
    (x : Erdos249257.BooleanMobiusGlobalRepairTrajectory) :
    (BooleanMobiusGlobalRepairTrajectory_transport_ofSrc x).bit = x.bit := rfl

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

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.signedDyadicValue` is the same function. -/
theorem signedDyadicValue_transport_def : @signedDyadicValue = @Erdos249257.signedDyadicValue := by
  first
  | (rfl; done)
  | (simp only [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (with_unfolding_all rfl; done)
  | (unfold signedDyadicValue Erdos249257.signedDyadicValue; done)
  | (unfold signedDyadicValue Erdos249257.signedDyadicValue <;> simp only [Erdos249257.signedDyadicValue, *]; done)
  | (ext x; simp only [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a; fun_induction signedDyadicValue a <;> simp only [Erdos249257.signedDyadicValue, *]; done)
  | (funext a; induction a <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a; induction a <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a; induction a <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a; simp [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a b; fun_induction signedDyadicValue a b <;> simp only [Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; induction b <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; induction a generalizing b <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; induction b generalizing a <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b; simp [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (funext a b c; fun_induction signedDyadicValue a b c <;> simp only [Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction c <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [signedDyadicValue, Erdos249257.signedDyadicValue, *]; done)
  | (funext a b c; simp [signedDyadicValue, Erdos249257.signedDyadicValue]; done)
  | (simp [signedDyadicValue, Erdos249257.signedDyadicValue]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.GlobalBooleanMobiusRepairFeasible`, read through the structure maps, is the source. -/
@[simp] theorem GlobalBooleanMobiusRepairFeasible_transport_def (T : BooleanMobiusGlobalRepairTrajectory) :
    @Erdos249257.GlobalBooleanMobiusRepairFeasible (BooleanMobiusGlobalRepairTrajectory_transport_toSrc T) = @GlobalBooleanMobiusRepairFeasible T := by
  first
  | (rfl; done)
  | (simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible <;> simp only [Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (ext x; simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a; fun_induction GlobalBooleanMobiusRepairFeasible a <;> simp only [Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a; induction a <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a; induction a <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a; induction a <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a; simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a b; fun_induction GlobalBooleanMobiusRepairFeasible a b <;> simp only [Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b; simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (funext a b c; fun_induction GlobalBooleanMobiusRepairFeasible a b c <;> simp only [Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def, *]; done)
  | (funext a b c; simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (simp [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible <;> rfl; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible <;> with_unfolding_all rfl; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible <;> simp only [signedDyadicValue_transport_def] <;> rfl; done)
  | (simp only [GlobalBooleanMobiusRepairFeasible, Erdos249257.GlobalBooleanMobiusRepairFeasible, signedDyadicValue_transport_def] <;> rfl; done)
  | (unfold GlobalBooleanMobiusRepairFeasible Erdos249257.GlobalBooleanMobiusRepairFeasible <;> simp only [signedDyadicValue_transport_def] <;> set_option smartUnfolding false in with_unfolding_all rfl; done)

theorem paper_compatible_finite_row_conditions
    (T : BooleanMobiusGlobalRepairTrajectory) :
    GlobalBooleanMobiusRepairFeasible T ↔
      ((∀ n : ℕ, 2 ≤ n →
          2 ^ (endpointDivisorContribution
                (globalRepairLowerSupport T.bit n) n - 1) - 1 ≤
            localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1)) ∧
       (∀ n : ℕ, 2 ≤ n →
          ((∑ d ∈ (globalRepairStageSupport T.bit n).filter
                (fun d ↦ n / 2 < d), 2 ^ (n - d) : ℕ) : ℤ) =
            localRepairInteger (globalRepairLowerSupport T.bit n) 1 n) ∧
       (∀ n : ℕ, 2 ≤ n →
          localRepairInteger (globalRepairLowerSupport T.bit n) 1 n <
            ((2 ^ (n - n / 2) : ℕ) : ℤ)) ∧
       (∀ n : ℕ, 2 ≤ n →
          localPrefixQuotient (globalRepairStageSupport T.bit n) n =
            2 ^ (n - 1) - 1)) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_finite_row_conditions (BooleanMobiusGlobalRepairTrajectory_transport_toSrc T)

theorem paper_largest_false_rank_algebra :
    (∀ (s d : ℕ) (u : Finset ℕ), 2 ≤ d → d < s → (∀ e ∈ u, 2 ≤ e ∧ e < d) →
        2 * s < 3 * d →
        3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
            + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
          = 3 * rowWeightSum s (insert d u)) ∧
    (∀ (s d : ℕ) (hs : 5 ≤ s), IsLargestFalseRank (seamGreedyWord s) d →
        ¬ SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) d) ∧
    (∀ (s : ℕ) (hs : 5 ≤ s), SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) s) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_largest_false_rank_algebra

end PalomarCorpus.E257.PaperStructuresBH
