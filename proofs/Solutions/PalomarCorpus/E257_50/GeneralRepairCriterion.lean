/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.GreedyRepairCriterion
import Solutions.PalomarCorpus.E257_50.Statement

open Set

namespace PalomarCorpus.E257.GeneralRepairCriterion
export PalomarCorpus.E257_50.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)

noncomputable section

theorem mersenneWeight_eq : mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight := rfl

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

theorem supportCoeff_eq : supportCoeff = Erdos257PeriodNoncollapse.supportCoeff := rfl

theorem binaryCoeffPrefixNumerator_eq :
    binaryCoeffPrefixNumerator = Erdos257PeriodNoncollapse.binaryCoeffPrefixNumerator := by
  funext c N
  induction N with
  | zero => rfl
  | succ N ih =>
    show 2 * binaryCoeffPrefixNumerator c N + c (N + 1) = _
    rw [ih]
    rfl

theorem greedyBinaryDefect_eq :
    greedyBinaryDefect = ErdosProblems.Erdos257.greedyBinaryDefect := by
  funext x N
  simp only [greedyBinaryDefect, ErdosProblems.Erdos257.greedyBinaryDefect,
    greedyMersenneSupport_eq, supportCoeff_eq, binaryCoeffPrefixNumerator_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue = Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

/-- Membership is cofinal non-increase of the greedy defect. -/
theorem mem_iff_greedyBinaryDefect_cofinal_repairs {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_cofinal_repairs hx

/-- The same criterion inside every window of width `2*sqrt K + 12`. -/
theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows hx

end

end PalomarCorpus.E257.GeneralRepairCriterion
