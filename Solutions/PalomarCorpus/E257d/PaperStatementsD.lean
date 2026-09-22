/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.CertificateKernel
import Erdos249257.CofinalStripReturn
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderFixedTailSocket
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap
import Solutions.PalomarCorpus.E257d.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsD

theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn hreturn

theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound hnonneg hbound

theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound hbound

theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg N

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem

theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := by
  set_option smartUnfolding false in
  exact @Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess n

theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_iff_every_actual_skip_survives

theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips hskips

theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry C D h

theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival

end PalomarCorpus.E257.PaperStatementsD
