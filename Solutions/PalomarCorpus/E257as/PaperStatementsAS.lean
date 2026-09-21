/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFloorErrorReset
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderSeamLimit
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit
import Solutions.PalomarCorpus.E257as.Statement

open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAS

theorem paper_seam_limit_unconditional :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) ∧
      Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) ∧
      seamGreedyLimitDeficit = 1 / 2 - greedyHalfTargetValue ∧
      0 ≤ seamGreedyLimitDeficit ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        Tendsto seamGreedyNormalizedRemainder atTop (nhds 0)) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_limit_unconditional

theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card := @ErdosProblems.Erdos257.PaperCompleteR21.paper_sharper_additive_estimate D c hc hD hbelow hskip

theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded E n hE habove

theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit D c hc hD hbelow hskip

theorem tendsto_seamGreedyFiniteValue_greedyHalfTargetValue :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) := @ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyFiniteValue_greedyHalfTargetValue

theorem tendsto_seamGreedyNormalizedRemainder :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) := @ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyNormalizedRemainder

end PalomarCorpus.E257.PaperStatementsAS
