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
import Solutions.PalomarCorpus.E257_06.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresAZ
export PalomarCorpus.E257_06.Shared (IsRowLower IsRowUpper localMersenneQuotient localPrefixQuotient rowPulse seamSubsetTarget truncatedMersenneWeight)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList` is the same function. -/
theorem SeamRowWord_ofList_transport_def : @SeamRowWord.ofList = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.ofList Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList; done)
  | (unfold SeamRowWord.ofList Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (ext x; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a; fun_induction SeamRowWord.ofList a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b; fun_induction SeamRowWord.ofList a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b c; fun_induction SeamRowWord.ofList a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord` is the same function. -/
theorem SeamRowWord_toNatWord_transport_def : @SeamRowWord.toNatWord = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (ext x; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a; fun_induction SeamRowWord.toNatWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b; fun_induction SeamRowWord.toNatWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b c; fun_induction SeamRowWord.toNatWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits` is the same function. -/
theorem integerGreedyBits_transport_def : @integerGreedyBits = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits := by
  first
  | (rfl; done)
  | (simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (ext x; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a; fun_induction integerGreedyBits a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b; fun_induction integerGreedyBits a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyBits a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom` is the same function. -/
theorem seamWeightsFrom_transport_def : @seamWeightsFrom = @Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom := by
  first
  | (rfl; done)
  | (simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (ext x; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; fun_induction seamWeightsFrom a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; fun_induction seamWeightsFrom a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; fun_induction seamWeightsFrom a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeights` is the same function. -/
theorem seamWeights_transport_def : @seamWeights = @Erdos249257.HalfCylinderIntegerGreedy.seamWeights := by
  first
  | (rfl; done)
  | (simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (ext x; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; fun_induction seamWeights a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; fun_induction seamWeights a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; fun_induction seamWeights a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord` is the same function. -/
theorem seamGreedyWord_transport_def : @seamGreedyWord = @Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord := by
  first
  | (rfl; done)
  | (simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord; done)
  | (unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (ext x; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; fun_induction seamGreedyWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; fun_induction seamGreedyWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; fun_induction seamGreedyWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)
  | (funext v1; unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord <;> simp only [SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.greedySupport` is the same function. -/
theorem greedySupport_transport_def : @greedySupport = @ErdosProblems.Erdos257.PaperCompleteR21.greedySupport := by
  first
  | (rfl; done)
  | (simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport; done)
  | (unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (ext x; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a; fun_induction greedySupport a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b; fun_induction greedySupport a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b c; fun_induction greedySupport a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def] <;> rfl; done)
  | (funext v1; unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport <;> simp only [SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def] <;> rfl; done)

theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics n hn D B D' hD hB hD' r o pm pp rem hr ho hpm hpp hrem

theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule n hn d hd hdn

theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower n hn

theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem n d hd hdn

theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step n d hd C

end PalomarCorpus.E257.PaperStructuresAZ
