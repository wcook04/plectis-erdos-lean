/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.BatchReturnSynthesis
import Solutions.PalomarCorpus.E257.Shared

open Set

namespace PalomarCorpus.E257.FourNinthsRepairWindows
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)

noncomputable section

noncomputable def fourNinthsBinaryFloor (N : ℕ) : ℕ :=
  4 * 2 ^ N / 9

noncomputable def fourNinthsGreedyDefect (N : ℕ) : ℕ :=
  fourNinthsBinaryFloor N -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ))) N

noncomputable def FourNinthsOneStepRepairSucc (N : ℕ) : Prop :=
  (fourNinthsGreedyDefect (N + 1) : ℤ) ≤ (fourNinthsGreedyDefect N : ℤ)

noncomputable def FourNinthsOneStepRepairCofinal : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ FourNinthsOneStepRepairSucc N

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

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue = Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem fourNinthsBinaryFloor_eq :
    fourNinthsBinaryFloor = ErdosProblems.Erdos257.fourNinthsBinaryFloor := rfl

theorem fourNinthsGreedyDefect_eq :
    fourNinthsGreedyDefect = ErdosProblems.Erdos257.fourNinthsGreedyDefect := by
  funext N
  simp only [fourNinthsGreedyDefect, ErdosProblems.Erdos257.fourNinthsGreedyDefect,
    fourNinthsBinaryFloor_eq, greedyMersenneSupport_eq, supportCoeff_eq,
    binaryCoeffPrefixNumerator_eq]

theorem FourNinthsOneStepRepairSucc_eq :
    FourNinthsOneStepRepairSucc = ErdosProblems.Erdos257.FourNinthsOneStepRepairSucc := by
  funext N
  simp only [FourNinthsOneStepRepairSucc, ErdosProblems.Erdos257.FourNinthsOneStepRepairSucc,
    fourNinthsGreedyDefect_eq]

theorem FourNinthsOneStepRepairCofinal_eq :
    FourNinthsOneStepRepairCofinal = ErdosProblems.Erdos257.FourNinthsOneStepRepairCofinal := by
  unfold FourNinthsOneStepRepairCofinal ErdosProblems.Erdos257.FourNinthsOneStepRepairCofinal
  rw [FourNinthsOneStepRepairSucc_eq]

theorem exists_repair_in_sqrt_window
    (Q : ℕ → ℕ)
    (hQ : ∀ N, (Q N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4)
    (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧ Q (N + 1) ≤ Q N :=
  ErdosProblems.Erdos257.exists_repair_in_sqrt_window Q hQ K

theorem four_ninths_mem_iff_repairCofinal :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔ FourNinthsOneStepRepairCofinal := by
  rw [mersenneAchievementSet_eq, FourNinthsOneStepRepairCofinal_eq]
  exact ErdosProblems.Erdos257.four_ninths_mem_iff_repairCofinal

theorem four_ninths_mem_iff_repair_sqrt_windows :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        FourNinthsOneStepRepairSucc N := by
  rw [mersenneAchievementSet_eq, FourNinthsOneStepRepairSucc_eq]
  exact ErdosProblems.Erdos257.four_ninths_mem_iff_repair_sqrt_windows

theorem four_ninths_not_mem_of_strict_sqrt_window
    (K : ℕ)
    (h : ∀ N, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      fourNinthsGreedyDefect N < fourNinthsGreedyDefect (N + 1)) :
    (4 / 9 : ℝ) ∉ mersenneAchievementSet := by
  rw [mersenneAchievementSet_eq]
  apply ErdosProblems.Erdos257.four_ninths_not_mem_of_strict_sqrt_window K
  intro N hKN hN
  simpa [fourNinthsGreedyDefect_eq] using h N hKN hN

end

end PalomarCorpus.E257.FourNinthsRepairWindows
