/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.TwentyOneQuotientCompactness
import Erdos249257.TwentyOneQuotientGreedy
import Solutions.PalomarCorpus.E257_39.Statement

open Filter
open Set
open scoped Classical
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBM
export PalomarCorpus.E257_39.Shared (TwentyOneCofinalEvenQuotientGreedyDecay integerGreedyBits integerGreedyRemainder localMersenneQuotient localMersenneWeights localMersenneWeightsFrom mersenneAchievementSet mersenneWeight positiveMersenneSupportValue twentyOneEvenQuotientGreedyRemainder twentyOneQuotientTarget weightedBoolSum)

theorem localMersenneWeightsFrom_transport_def : @localMersenneWeightsFrom = @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom := by
  first
  | (rfl; done)
  | (simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (with_unfolding_all rfl; done)
  | (unfold localMersenneWeightsFrom Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom; done)
  | (unfold localMersenneWeightsFrom Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (ext x; simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a; fun_induction localMersenneWeightsFrom a <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a; induction a <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a; induction a <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a; induction a <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a; simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a b; fun_induction localMersenneWeightsFrom a b <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; induction b <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; induction a generalizing b <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; induction b generalizing a <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b; simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (funext a b c; fun_induction localMersenneWeightsFrom a b c <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction c <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, *]; done)
  | (funext a b c; simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)
  | (simp [localMersenneWeightsFrom, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights` is the same function. -/
theorem localMersenneWeights_transport_def : @localMersenneWeights = @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights := by
  first
  | (rfl; done)
  | (simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold localMersenneWeights Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights; done)
  | (unfold localMersenneWeights Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (ext x; simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a; fun_induction localMersenneWeights a <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a; simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a b; fun_induction localMersenneWeights a b <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b; simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (funext a b c; fun_induction localMersenneWeights a b c <;> simp only [Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def, *]; done)
  | (funext a b c; simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)
  | (simp [localMersenneWeights, Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, localMersenneWeightsFrom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits` is the same function. -/
theorem integerGreedyBits_transport_def : @integerGreedyBits = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits := by
  first
  | (rfl; done)
  | (simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (ext x; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a; fun_induction integerGreedyBits a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b; fun_induction integerGreedyBits a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyBits a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum` is the same function. -/
theorem weightedBoolSum_transport_def : @weightedBoolSum = @Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum := by
  first
  | (rfl; done)
  | (simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (ext x; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; fun_induction weightedBoolSum a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; fun_induction weightedBoolSum a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; fun_induction weightedBoolSum a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)
  | (simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder` is the same function. -/
theorem integerGreedyRemainder_transport_def : @integerGreedyRemainder = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (ext x; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; fun_induction integerGreedyRemainder a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; fun_induction integerGreedyRemainder a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyRemainder a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.twentyOneEvenQuotientGreedyRemainder` is the same function. -/
theorem twentyOneEvenQuotientGreedyRemainder_transport_def : @twentyOneEvenQuotientGreedyRemainder = @Erdos249257.twentyOneEvenQuotientGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold twentyOneEvenQuotientGreedyRemainder Erdos249257.twentyOneEvenQuotientGreedyRemainder; done)
  | (unfold twentyOneEvenQuotientGreedyRemainder Erdos249257.twentyOneEvenQuotientGreedyRemainder <;> simp only [Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (ext x; simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a; fun_induction twentyOneEvenQuotientGreedyRemainder a <;> simp only [Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a; simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b; fun_induction twentyOneEvenQuotientGreedyRemainder a b <;> simp only [Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b; simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (funext a b c; fun_induction twentyOneEvenQuotientGreedyRemainder a b c <;> simp only [Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, *]; done)
  | (funext a b c; simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (simp [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [twentyOneEvenQuotientGreedyRemainder, Erdos249257.twentyOneEvenQuotientGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def] <;> rfl; done)
  | (funext v1; unfold twentyOneEvenQuotientGreedyRemainder Erdos249257.twentyOneEvenQuotientGreedyRemainder <;> simp only [localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay` is the same function. -/
theorem TwentyOneCofinalEvenQuotientGreedyDecay_transport_def : @TwentyOneCofinalEvenQuotientGreedyDecay = @Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay := by
  first
  | (rfl; done)
  | (simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold TwentyOneCofinalEvenQuotientGreedyDecay Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay; done)
  | (unfold TwentyOneCofinalEvenQuotientGreedyDecay Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay <;> simp only [Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (ext x; simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a; fun_induction TwentyOneCofinalEvenQuotientGreedyDecay a <;> simp only [Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a; simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a b; fun_induction TwentyOneCofinalEvenQuotientGreedyDecay a b <;> simp only [Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b; simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (funext a b c; fun_induction TwentyOneCofinalEvenQuotientGreedyDecay a b c <;> simp only [Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def, *]; done)
  | (funext a b c; simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)
  | (simp [TwentyOneCofinalEvenQuotientGreedyDecay, Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def, twentyOneEvenQuotientGreedyRemainder_transport_def]; done)

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyDecay) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay hcofinal

end PalomarCorpus.E257.PaperStructuresBM
