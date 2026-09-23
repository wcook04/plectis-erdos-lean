/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.RecordJumpEnergySeries
import ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import Solutions.PalomarCorpus.E243_04.Statement
import Solutions.PalomarCorpus.E243_04.PaperStructuresT

open Filter
open scoped BigOperators
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresU
export PalomarCorpus.E243_04.Shared (canonicalDenominator canonicalNaturalNumerator clearedIntegerNumerator prefixProduct)

noncomputable def StandingOrbit.jump (O : StandingOrbit) (n : ℕ) : ℕ := O.u (n + 1) - O.u n

noncomputable def StandingOrbit.energy (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then
    (if 3 ≤ O.jump n then 1 / Real.sqrt ((O.u n : ℝ)) else 0)
      + ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ)
  else 0

noncomputable def StandingOrbit.energySqrt (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ))
  else 0

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

@[simp] theorem StandingOrbit_G_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G (StandingOrbit_transport_toSrc O) = StandingOrbit.G O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.G a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.G a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.G a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)

@[simp] theorem StandingOrbit_u_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u (StandingOrbit_transport_toSrc O) = StandingOrbit.u O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.u a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.u a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.u a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)
  | (simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def]; done)

/-- The local copy of `ErdosProblems.Erdos243.runningMax` is the same function. -/
theorem runningMax_transport_def : @runningMax = @ErdosProblems.Erdos243.runningMax := by
  first
  | (rfl; done)
  | (simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; fun_induction runningMax a <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; induction a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; fun_induction runningMax a b <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; fun_induction runningMax a b c <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)

@[simp] theorem StandingOrbit_Hmax_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax (StandingOrbit_transport_toSrc O) = StandingOrbit.Hmax O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.Hmax a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.Hmax a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.Hmax a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (simp [StandingOrbit.Hmax, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Hmax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)

@[simp] theorem StandingOrbit_R_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R (StandingOrbit_transport_toSrc O) = StandingOrbit.R O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.R a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.R a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.R a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)
  | (simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def]; done)

@[simp] theorem StandingOrbit_jump_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump (StandingOrbit_transport_toSrc O) = StandingOrbit.jump O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.jump a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.jump a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.jump a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)
  | (simp [StandingOrbit.jump, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.jump, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def]; done)

@[simp] theorem StandingOrbit_energy_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy (StandingOrbit_transport_toSrc O) = StandingOrbit.energy O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.energy a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.energy a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.energy a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)
  | (simp [StandingOrbit.energy, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def]; done)

@[simp] theorem StandingOrbit_energySqrt_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt (StandingOrbit_transport_toSrc O) = StandingOrbit.energySqrt O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.energySqrt a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.energySqrt a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.energySqrt a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)
  | (simp [StandingOrbit.energySqrt, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def]; done)

@[simp] theorem StandingOrbit_v_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v (StandingOrbit_transport_toSrc O) = StandingOrbit.v O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.v a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.v a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.v a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)
  | (simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def]; done)

theorem energySqrt_summable_iff (O : StandingOrbit) :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt_summable_iff (StandingOrbit_transport_toSrc O)

theorem energy_criterion (O : StandingOrbit) :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_criterion (StandingOrbit_transport_toSrc O)

theorem energy_le_two_energySqrt (O : StandingOrbit) (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_le_two_energySqrt (StandingOrbit_transport_toSrc O) n

theorem energy_summable_iff (O : StandingOrbit) :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_summable_iff (StandingOrbit_transport_toSrc O)

theorem exists_late_energy_window (O : StandingOrbit) (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.exists_late_energy_window (StandingOrbit_transport_toSrc O) hunb S

theorem oddPrimePower_supply (O : StandingOrbit) (A : ℝ) (hA : 0 < A) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ Odd (p ^ k) ∧
      p ^ k ∣ O.v n ∧ ((O.Hmax n : ℝ) + 2) ^ A < ((p ^ k : ℕ) : ℝ) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply (StandingOrbit_transport_toSrc O) A hA

theorem oddPrimePower_supply_nat (O : StandingOrbit) (A : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧
      p ^ k ∣ O.v n ∧ (O.Hmax n + 2) ^ A < p ^ k := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply_nat (StandingOrbit_transport_toSrc O) A

theorem unitRecordIncrement_criterion (O : StandingOrbit) :
    (∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ↔
      {n : ℕ | 2 ≤ O.R (n + 1) - O.R n}.Finite := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_Hmax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_jump_transport_def, StandingOrbit_energy_transport_def, StandingOrbit_energySqrt_transport_def, StandingOrbit_v_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_criterion (StandingOrbit_transport_toSrc O)

end PalomarCorpus.E243.PaperStructuresU
