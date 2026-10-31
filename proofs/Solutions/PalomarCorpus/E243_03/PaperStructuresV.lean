/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.AmplifiedRecordEquivalence
import ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import Solutions.PalomarCorpus.E243_03.Statement
import Solutions.PalomarCorpus.E243_03.PaperStructuresT

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresV
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator clearedIntegerNumerator prefixProduct)

/-- The copied structure `StandingOrbit` and its source `ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit` carry the same
fields, so each converts into the other field by field. -/
noncomputable def StandingOrbit_transport_toSrc (x : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit :=
  ⟨x.a, x.num, x.den, x.a_strictMono, x.a_pos, x.den_pos, x.hasSum, x.growth⟩

/-- The inverse of `StandingOrbit_transport_toSrc`. -/
noncomputable def StandingOrbit_transport_ofSrc (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    StandingOrbit :=
  ⟨x.a, x.num, x.den, x.a_strictMono, x.a_pos, x.den_pos, x.hasSum, x.growth⟩

@[simp] theorem StandingOrbit_transport_toSrc_a
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).a = x.a := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_a
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).a = x.a := rfl

@[simp] theorem StandingOrbit_transport_toSrc_num
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).num = x.num := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_num
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).num = x.num := rfl

@[simp] theorem StandingOrbit_transport_toSrc_den
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).den = x.den := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_den
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).den = x.den := rfl

@[simp] theorem StandingOrbit_C_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C (StandingOrbit_transport_toSrc O) = StandingOrbit.C O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a; fun_induction StandingOrbit.C a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b; fun_induction StandingOrbit.C a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b c; fun_induction StandingOrbit.C a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b c; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)

@[simp] theorem StandingOrbit_D_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D (StandingOrbit_transport_toSrc O) = StandingOrbit.D O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.D a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.D a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.D a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)

@[simp] theorem StandingOrbit_EventuallySylvester_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester (StandingOrbit_transport_toSrc O) = StandingOrbit.EventuallySylvester O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.EventuallySylvester a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.EventuallySylvester a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.EventuallySylvester a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)

@[simp] theorem StandingOrbit_G_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G (StandingOrbit_transport_toSrc O) = StandingOrbit.G O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.G a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.G a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.G a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)

@[simp] theorem StandingOrbit_u_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u (StandingOrbit_transport_toSrc O) = StandingOrbit.u O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.u a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.u a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.u a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)

/-- The local copy of `ErdosProblems.Erdos243.runningMax` is the same function. -/
theorem runningMax_transport_def : @runningMax = @ErdosProblems.Erdos243.runningMax := by
  first
  | (rfl; done)
  | (simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; fun_induction runningMax a <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; induction a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; fun_induction runningMax a b <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; fun_induction runningMax a b c <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)

@[simp] theorem StandingOrbit_R_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R (StandingOrbit_transport_toSrc O) = StandingOrbit.R O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.R a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.R a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.R a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)

@[simp] theorem StandingOrbit_v_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v (StandingOrbit_transport_toSrc O) = StandingOrbit.v O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.v a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.v a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.v a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)

@[simp] theorem StandingOrbit_redErr_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr (StandingOrbit_transport_toSrc O) = StandingOrbit.redErr O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.redErr a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.redErr a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.redErr a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)

@[simp] theorem StandingOrbit_negPart_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart (StandingOrbit_transport_toSrc O) = StandingOrbit.negPart O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.negPart a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.negPart a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.negPart a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)

@[simp] theorem StandingOrbit_amp_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp (StandingOrbit_transport_toSrc O) = StandingOrbit.amp O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.amp a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.amp a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.amp a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)

@[simp] theorem StandingOrbit_canc_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc (StandingOrbit_transport_toSrc O) = StandingOrbit.canc O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.canc a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.canc a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.canc a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)

theorem canc_lt_of_amp_le (O : StandingOrbit) (hns : ¬ O.EventuallySylvester) (K : ℕ) (hK1 : 1 ≤ K)
    (N₀ : ℕ) (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) :
    ∃ N, ∀ s, N ≤ s → O.canc s < 2 * K := by
  simp only [← StandingOrbit_transport_toSrc_a, ← StandingOrbit_transport_toSrc_den, ← StandingOrbit_transport_toSrc_num, ← StandingOrbit_C_transport_def, ← StandingOrbit_D_transport_def, ← StandingOrbit_EventuallySylvester_transport_def, ← StandingOrbit_G_transport_def, ← StandingOrbit_u_transport_def, ← runningMax_transport_def, ← StandingOrbit_R_transport_def, ← StandingOrbit_v_transport_def, ← StandingOrbit_redErr_transport_def, ← StandingOrbit_negPart_transport_def, ← StandingOrbit_amp_transport_def, ← StandingOrbit_canc_transport_def] at *
  exact @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc_lt_of_amp_le (StandingOrbit_transport_toSrc O) hns K hK1 N₀ hbd

theorem eventuallySylvester_of_amp_le (O : StandingOrbit) (K : ℕ) (hK1 : 1 ≤ K) (N₀ : ℕ)
    (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) : O.EventuallySylvester := by
  simp only [← StandingOrbit_transport_toSrc_a, ← StandingOrbit_transport_toSrc_den, ← StandingOrbit_transport_toSrc_num, ← StandingOrbit_C_transport_def, ← StandingOrbit_D_transport_def, ← StandingOrbit_EventuallySylvester_transport_def, ← StandingOrbit_G_transport_def, ← StandingOrbit_u_transport_def, ← runningMax_transport_def, ← StandingOrbit_R_transport_def, ← StandingOrbit_v_transport_def, ← StandingOrbit_redErr_transport_def, ← StandingOrbit_negPart_transport_def, ← StandingOrbit_amp_transport_def, ← StandingOrbit_canc_transport_def] at *
  exact @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.eventuallySylvester_of_amp_le (StandingOrbit_transport_toSrc O) K hK1 N₀ hbd

end PalomarCorpus.E243.PaperStructuresV
