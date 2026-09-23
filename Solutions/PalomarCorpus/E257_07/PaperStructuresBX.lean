/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics
import Solutions.PalomarCorpus.E257_07.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBX

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

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord` is the same function. -/
theorem SeamRowWord_toNatWord_transport_def : @SeamRowWord.toNatWord = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (ext x; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a; fun_induction SeamRowWord.toNatWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b; fun_induction SeamRowWord.toNatWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b c; fun_induction SeamRowWord.toNatWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)

theorem paper_upperSupport_isRowUpper {n : ℕ} (hn : 5 ≤ n) :
    IsRowUpper n (rowSupport n (seamAboveWord n hn)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_upperSupport_isRowUpper n hn

end PalomarCorpus.E257.PaperStructuresBX
