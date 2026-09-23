/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

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

/-- States res:one-over-twenty-one-frontier from the short record for Erdős problem #257.
Transported from
Erdos249257.one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyDecay) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBM
