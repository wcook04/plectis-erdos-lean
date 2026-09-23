/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Solutions.PalomarCorpus.E257_11.Statement

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsB
export PalomarCorpus.E257_11.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  set_option smartUnfolding false in
  exact @Erdos249257.greedy_survives_of_mem_mersenneAchievementSet x hx

theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite

theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation hseparate

theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven hseparate

theorem half_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfDyadicCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap hskip

theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap hskip

theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival x

theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite x hx hskips

theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_of_greedy_survival x hx hsurvive

end PalomarCorpus.E257.PaperStatementsB
