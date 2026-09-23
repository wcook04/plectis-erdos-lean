/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCarryRewindPhase
import Erdos249257.HalfCarrySelectedWindow
import Erdos249257.SelectedSuffixCylinder
import Erdos249257.SuffixCylinderThreshold
import ErdosProblems.Erdos257.PaperCompleteR21.SharedPrefixFamiliesAndMeasureDichotomy
import Solutions.PalomarCorpus.E257_34.Statement
import Solutions.PalomarCorpus.E257_34.PaperStructuresBR

open MeasureTheory
open Set
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBT
export PalomarCorpus.E257_34.Shared (CylinderStage HalfStripAdmissible HalfWord HasSuffixCylinderAt SelectedHalfWindow affineBinaryOrbit halfStripBound integerHalfCarry restrictWord supportCoeff supportSuffixNumeral wordSuffixNumeral wordSupport)

noncomputable def SelectedHalfWindow_transport_toSrc {N R : ℕ} (x : SelectedHalfWindow N R) :
    Erdos249257.HalfCarrySelectedWindow.SelectedHalfWindow N R :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The inverse of `SelectedHalfWindow_transport_toSrc`. -/
noncomputable def SelectedHalfWindow_transport_ofSrc {N R : ℕ} (x : Erdos249257.HalfCarrySelectedWindow.SelectedHalfWindow N R) :
    SelectedHalfWindow N R :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The copied structure `CylinderStage` and its source `Erdos249257.SuffixCylinderThreshold.CylinderStage` carry the same
fields, so each converts into the other field by field. -/
noncomputable def CylinderStage_transport_toSrc {K N : ℕ} (x : CylinderStage K N) :
    Erdos249257.SuffixCylinderThreshold.CylinderStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hKN), (SelectedHalfWindow_transport_toSrc x.window), x.endpoint, (by set_option smartUnfolding false in with_unfolding_all exact x.cylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.covers)⟩

/-- The inverse of `CylinderStage_transport_toSrc`. -/
noncomputable def CylinderStage_transport_ofSrc {K N : ℕ} (x : Erdos249257.SuffixCylinderThreshold.CylinderStage K N) :
    CylinderStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hKN), (SelectedHalfWindow_transport_ofSrc x.window), x.endpoint, (by set_option smartUnfolding false in with_unfolding_all exact x.cylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.covers)⟩

@[simp] theorem CylinderStage_transport_toSrc_endpoint {K N : ℕ}
    (x : CylinderStage K N) :
    (CylinderStage_transport_toSrc x).endpoint = x.endpoint := rfl

@[simp] theorem CylinderStage_transport_ofSrc_endpoint {K N : ℕ}
    (x : Erdos249257.SuffixCylinderThreshold.CylinderStage K N) :
    (CylinderStage_transport_ofSrc x).endpoint = x.endpoint := rfl

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral` is the same function. -/
theorem supportSuffixNumeral_transport_def : @supportSuffixNumeral = @Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral := by
  first
  | (rfl; done)
  | (simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (with_unfolding_all rfl; done)
  | (unfold supportSuffixNumeral Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral; done)
  | (unfold supportSuffixNumeral Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (ext x; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a; fun_induction supportSuffixNumeral a <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b; fun_induction supportSuffixNumeral a b <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction a generalizing b <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b generalizing a <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b c; fun_induction supportSuffixNumeral a b c <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3 v4; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3 v4; fun_induction supportSuffixNumeral v1 v2 v3 v4 <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v1 generalizing v2 v3 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v2 generalizing v1 v3 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v3 generalizing v1 v2 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v4 generalizing v1 v2 v3 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.affineBinaryOrbit` is the same function. -/
theorem affineBinaryOrbit_transport_def : @affineBinaryOrbit = @Erdos249257.affineBinaryOrbit := by
  first
  | (rfl; done)
  | (simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (ext x; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a; fun_induction affineBinaryOrbit a <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b; fun_induction affineBinaryOrbit a b <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b c; fun_induction affineBinaryOrbit a b c <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.integerHalfCarry` is the same function. -/
theorem integerHalfCarry_transport_def : @integerHalfCarry = @Erdos249257.HalfCarryReachability.integerHalfCarry := by
  first
  | (rfl; done)
  | (simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (ext x; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a; fun_induction integerHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b; fun_induction integerHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; fun_induction integerHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.HalfStripAdmissible` is the same function. -/
theorem HalfStripAdmissible_transport_def : @HalfStripAdmissible = @Erdos249257.HalfCarryReachability.HalfStripAdmissible := by
  first
  | (rfl; done)
  | (simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible; done)
  | (unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (ext x; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; fun_induction HalfStripAdmissible a <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; fun_induction HalfStripAdmissible a b <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction HalfStripAdmissible a b c <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1; unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral` is the same function. -/
theorem wordSuffixNumeral_transport_def : @wordSuffixNumeral = @Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral := by
  first
  | (rfl; done)
  | (simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral; done)
  | (unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (ext x; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a; fun_induction wordSuffixNumeral a <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b; fun_induction wordSuffixNumeral a b <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b c; fun_induction wordSuffixNumeral a b c <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; fun_induction wordSuffixNumeral v1 v2 v3 v4 <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v1 generalizing v2 v3 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v2 generalizing v1 v3 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v3 generalizing v1 v2 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v4 generalizing v1 v2 v3 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt`, read through the structure maps, is the source. -/
@[simp] theorem HasSuffixCylinderAt_transport_def {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N) (endpoint : ℕ) :
    @Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt M N R (SelectedHalfWindow_transport_toSrc W) hMN endpoint = @HasSuffixCylinderAt M N R W hMN endpoint := by
  first
  | (rfl; done)
  | (simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (ext x; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a; fun_induction HasSuffixCylinderAt a <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b; fun_induction HasSuffixCylinderAt a b <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b c; fun_induction HasSuffixCylinderAt a b c <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> rfl; done)
  | (simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> set_option smartUnfolding false in with_unfolding_all rfl; done)

theorem paper_shared_prefix_family_contains_strip_witness
    {K N : ℕ} (S : CylinderStage K N) :
    ∃ a : HalfWord N,
      a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
        (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N - 1) : ℝ)| ≤
          (halfStripBound N : ℝ) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_contains_strip_witness K N (CylinderStage_transport_toSrc S)

end PalomarCorpus.E257.PaperStructuresBT
