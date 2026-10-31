/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.TwentyOneQuotientCompactness
import Erdos249257.TwentyOneQuotientGreedy

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusGreedyReduction`, `Erdos249257.BooleanMobiusLocalRepair`,
`Erdos249257.GreedyAchievementSet`, `Erdos249257.HalfCylinderIntegerGreedy`,
`Erdos249257.TwentyOneQuotientCompactness`, `Erdos249257.TwentyOneQuotientGreedy`.
-/

open Filter
open Set
open scoped Classical
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBM

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega

noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2

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

noncomputable def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21

noncomputable def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))

noncomputable def TwentyOneCofinalEvenQuotientGreedyDecay : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      Tendsto
        (fun k : ℕ =>
          ((twentyOneEvenQuotientGreedyRemainder (R k) +
              (2 * R k + 1) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k))
        atTop (nhds 0)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

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

end Erdos249257.ExternalVerification257PaperStructuresBM
