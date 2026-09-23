/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership
import ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip
import Solutions.PalomarCorpus.E257_25.Statement

open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBK

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

noncomputable def SeamResetSqrtEscape : Prop :=
  ∀ (r : ℕ) (hr5 : 5 ≤ r), 10 ≤ r →
    SeamGreedyUpperOrMiddleAt r hr5 →
      ((2 ^ (r + 5) : ℕ) : ℤ) < seamResetDeviation r ^ 2

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
/-- The local copy of `Erdos249257.affineBinaryOrbit` is the same function. -/
theorem affineBinaryOrbit_transport_def : @affineBinaryOrbit = @Erdos249257.affineBinaryOrbit := by
  first
  | (rfl; done)
  | (simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (with_unfolding_all rfl; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (ext x; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; fun_induction affineBinaryOrbit a <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; fun_induction affineBinaryOrbit a b <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; fun_induction affineBinaryOrbit a b c <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.integerHalfCarry` is the same function. -/
theorem integerHalfCarry_transport_def : @integerHalfCarry = @Erdos249257.HalfCarryReachability.integerHalfCarry := by
  first
  | (rfl; done)
  | (simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (ext x; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a; fun_induction integerHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b; fun_induction integerHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; fun_induction integerHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [affineBinaryOrbit_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry` is the same function. -/
theorem mobiusCenteredHalfCarry_transport_def : @mobiusCenteredHalfCarry = @Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry := by
  first
  | (rfl; done)
  | (simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold mobiusCenteredHalfCarry Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry; done)
  | (unfold mobiusCenteredHalfCarry Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (ext x; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; fun_induction mobiusCenteredHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; fun_induction mobiusCenteredHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction mobiusCenteredHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator` is the same function. -/
theorem finiteCoeffWindowNumerator_transport_def : @finiteCoeffWindowNumerator = @Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator := by
  first
  | (rfl; done)
  | (simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator; done)
  | (unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (ext x; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a; fun_induction finiteCoeffWindowNumerator a <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b; fun_induction finiteCoeffWindowNumerator a b <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction finiteCoeffWindowNumerator a b c <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)

theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape hsqrt

theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band n hn hskip hneg

theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative hescape

end PalomarCorpus.E257.PaperStructuresBK
