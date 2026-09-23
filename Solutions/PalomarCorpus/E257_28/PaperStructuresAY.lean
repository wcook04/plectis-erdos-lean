/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderIntegerGreedy
import Solutions.PalomarCorpus.E257_28.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresAY
export PalomarCorpus.E257_28.Shared (localMersenneQuotient)

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom` is the same function. -/
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
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.GapDominates` is the same function. -/
theorem GapDominates_transport_def : @GapDominates = @Erdos249257.HalfCylinderIntegerGreedy.GapDominates := by
  first
  | (rfl; done)
  | (simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold GapDominates Erdos249257.HalfCylinderIntegerGreedy.GapDominates; done)
  | (unfold GapDominates Erdos249257.HalfCylinderIntegerGreedy.GapDominates <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (ext x; simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a; fun_induction GapDominates a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a; simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b; fun_induction GapDominates a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b; simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (funext a b c; fun_induction GapDominates a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, *]; done)
  | (funext a b c; simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)
  | (simp [GapDominates, Erdos249257.HalfCylinderIntegerGreedy.GapDominates, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits` is the same function. -/
theorem integerGreedyBits_transport_def : @integerGreedyBits = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits := by
  first
  | (rfl; done)
  | (simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (ext x; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a; fun_induction integerGreedyBits a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a b; fun_induction integerGreedyBits a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyBits a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)
  | (simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum` is the same function. -/
theorem weightedBoolSum_transport_def : @weightedBoolSum = @Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum := by
  first
  | (rfl; done)
  | (simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum; done)
  | (unfold weightedBoolSum Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (ext x; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; fun_induction weightedBoolSum a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; fun_induction weightedBoolSum a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; fun_induction weightedBoolSum a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)
  | (simp [weightedBoolSum, Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder` is the same function. -/
theorem integerGreedyRemainder_transport_def : @integerGreedyRemainder = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder; done)
  | (unfold integerGreedyRemainder Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (ext x; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a; fun_induction integerGreedyRemainder a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b; fun_induction integerGreedyRemainder a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyRemainder a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)
  | (simp [integerGreedyRemainder, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def]; done)

theorem localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
    {M R A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        2 ^ (M - 1) - 1)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) := by
  simp only [localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def] at *
  exact @Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq M R A bits hRM hlen hfill hA

theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d) := by
  simp only [localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]
  exact @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates M R d hRM hd

theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R) := by
  simp only [localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]
  exact @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even R hR

theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R) := by
  simp only [localMersenneWeightsFrom_transport_def, localMersenneWeights_transport_def, GapDominates_transport_def, integerGreedyBits_transport_def, weightedBoolSum_transport_def, integerGreedyRemainder_transport_def]
  exact @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd R

end PalomarCorpus.E257.PaperStructuresAY
