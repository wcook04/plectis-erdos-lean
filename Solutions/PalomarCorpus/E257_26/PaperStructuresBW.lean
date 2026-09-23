/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip
import Solutions.PalomarCorpus.E257_26.Statement

open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBW
export PalomarCorpus.E257_26.Shared (greedyMersenneRemainder halfStripBound mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

theorem integerGreedyBits_transport_def : @integerGreedyBits = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits := by
  first
  | (rfl; done)
  | (simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (ext x; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a; fun_induction integerGreedyBits a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a; induction a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a b; fun_induction integerGreedyBits a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (funext a b c; fun_induction integerGreedyBits a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, *]; done)
  | (funext a b c; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)
  | (simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum` is the same function. -/
theorem weightedBoolSum_transport_def : @weightedBoolSum = @Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum := by
  first
  | (rfl; done)
  | (simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (ext x; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a; fun_induction weightedBoolSum a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a b; fun_induction weightedBoolSum a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (funext a b c; fun_induction weightedBoolSum a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)
  | (simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, integerGreedyBits_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder` is the same function. -/
theorem integerGreedyRemainder_transport_def : @integerGreedyRemainder = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (ext x; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; fun_induction integerGreedyRemainder a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; fun_induction integerGreedyRemainder a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyRemainder a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom` is the same function. -/
theorem seamWeightsFrom_transport_def : @seamWeightsFrom = @Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom := by
  first
  | (rfl; done)
  | (simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (ext x; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a; fun_induction seamWeightsFrom a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b; fun_induction seamWeightsFrom a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b c; fun_induction seamWeightsFrom a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeights` is the same function. -/
theorem seamWeights_transport_def : @seamWeights = @Erdos249257.HalfCylinderIntegerGreedy.seamWeights := by
  first
  | (rfl; done)
  | (simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (ext x; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; fun_induction seamWeights a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; fun_induction seamWeights a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; fun_induction seamWeights a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)
  | (simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder` is the same function. -/
theorem seamIntegerGreedyRemainder_transport_def : @seamIntegerGreedyRemainder = @Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamIntegerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder; done)
  | (unfold seamIntegerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (ext x; simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; fun_induction seamIntegerGreedyRemainder a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; fun_induction seamIntegerGreedyRemainder a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; fun_induction seamIntegerGreedyRemainder a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (simp [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [seamIntegerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)
  | (funext v1; unfold seamIntegerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder <;> simp only [integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.greedyMersenneRemainder` is the same function. -/
theorem greedyMersenneRemainder_transport_def : @greedyMersenneRemainder = @Erdos249257.greedyMersenneRemainder := by
  first
  | (rfl; done)
  | (simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder; done)
  | (unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder <;> simp only [Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (ext x; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a; fun_induction greedyMersenneRemainder a <;> simp only [Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a b; fun_induction greedyMersenneRemainder a b <;> simp only [Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (funext a b c; fun_induction greedyMersenneRemainder a b c <;> simp only [Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def] <;> rfl; done)
  | (funext v1; unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder <;> simp only [integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder <;> simp only [integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamIntegerGreedyRemainder_transport_def] <;> rfl; done)

theorem paper_seam_escape_implies_half_membership
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership hescape

end PalomarCorpus.E257.PaperStructuresBW
