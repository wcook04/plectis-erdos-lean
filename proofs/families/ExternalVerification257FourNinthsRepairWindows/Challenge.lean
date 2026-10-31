/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for four-ninths square-root repair windows

A natural sequence in the square-root strip cannot strictly increase through a
window of length `2 * sqrt K + 12`. Specialising to the `4/9` greedy defect
gives exact equivalences: membership of `4/9` in the Mersenne achievement set
is equivalent to cofinal one-step repairs and to a repair in every explicit
square-root window. One certified window of strict increases excludes the
target. These are target-specific equivalences. They do not prove that the
repair producer holds, they are not the tetraprime `4/9` package, and they
do not settle Erdős #257.
-/

namespace Erdos249257.ExternalVerification257FourNinthsRepairWindows

open Set

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

def fourNinthsBinaryFloor (N : ℕ) : ℕ :=
  4 * 2 ^ N / 9

noncomputable def fourNinthsGreedyDefect (N : ℕ) : ℕ :=
  fourNinthsBinaryFloor N -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ))) N

def FourNinthsOneStepRepairSucc (N : ℕ) : Prop :=
  (fourNinthsGreedyDefect (N + 1) : ℤ) ≤ (fourNinthsGreedyDefect N : ℤ)

def FourNinthsOneStepRepairCofinal : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ FourNinthsOneStepRepairSucc N

/-- A natural sequence in the square-root strip cannot strictly increase
through a window of length `2 * sqrt K + 12`. -/
theorem exists_repair_in_sqrt_window
    (Q : ℕ → ℕ)
    (hQ : ∀ N, (Q N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4)
    (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧ Q (N + 1) ≤ Q N := by
  sorry

/-- The old sufficient producer is also necessary at `4/9`. -/
theorem four_ninths_mem_iff_repairCofinal :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔ FourNinthsOneStepRepairCofinal := by
  sorry

/-- A finite-window formulation exactly equivalent to `4/9` membership. -/
theorem four_ninths_mem_iff_repair_sqrt_windows :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        FourNinthsOneStepRepairSucc N := by
  sorry

/-- One certified window of strict increases excludes the target. -/
theorem four_ninths_not_mem_of_strict_sqrt_window
    (K : ℕ)
    (h : ∀ N, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      fourNinthsGreedyDefect N < fourNinthsGreedyDefect (N + 1)) :
    (4 / 9 : ℝ) ∉ mersenneAchievementSet := by
  sorry

end

end Erdos249257.ExternalVerification257FourNinthsRepairWindows
