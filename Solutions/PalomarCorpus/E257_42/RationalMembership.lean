/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.GreedyAchievementSet
import Solutions.PalomarCorpus.E257_42.Statement

open Set

namespace PalomarCorpus.E257.RationalMembership
export PalomarCorpus.E257_42.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

noncomputable section

theorem mersenneWeight_eq :
    mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight :=
  rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem greedyMersenneSkippedSupport_eq :
    greedyMersenneSkippedSupport =
      Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport := by
  funext x
  simp only [greedyMersenneSkippedSupport,
    Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport,
    greedyMersenneSupport_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue =
      Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem greedyMersenneSkippedSupport_infinite_iff_cofinal_skips (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  rw [greedyMersenneSkippedSupport_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport_infinite_iff_cofinal_skips x

theorem infinite_greedyMersenneSkippedSupport_of_rat_mem
    {q : ℚ} (hmem : (q : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq] at hmem
  rw [greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.infinite_greedyMersenneSkippedSupport_of_rat_mem hmem

theorem rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq, greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    q hq

theorem rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (q : ℝ) n := by
  rw [mersenneAchievementSet_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    q hq

end

end PalomarCorpus.E257.RationalMembership
