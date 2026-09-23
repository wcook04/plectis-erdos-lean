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
