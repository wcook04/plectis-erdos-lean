/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.BooleanMobiusSkipRowCofinal
import Solutions.PalomarCorpus.E257_50.Statement

open Set

namespace PalomarCorpus.E257.PositiveSkipEquivalence

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

private theorem greedyRemainderRat_transport (x : ℚ) (n : ℕ) :
    greedyMersenneRemainderRat x n =
      Erdos257PeriodNoncollapse.greedyMersenneRemainderRat x n := by
  induction n with
  | zero =>
      simp only [greedyMersenneRemainderRat,
        Erdos257PeriodNoncollapse.greedyMersenneRemainderRat]
  | succ n ih =>
      simp only [greedyMersenneRemainderRat,
        Erdos257PeriodNoncollapse.greedyMersenneRemainderRat, ih,
        show mersenneWeightRat = Erdos257PeriodNoncollapse.mersenneWeightRat from rfl]

private theorem cofinalPositiveHalfGreedySkips_transport :
    CofinalPositiveHalfGreedySkips =
      Erdos257PeriodNoncollapse.CofinalPositiveHalfGreedySkips := by
  simp only [CofinalPositiveHalfGreedySkips,
    Erdos257PeriodNoncollapse.CofinalPositiveHalfGreedySkips,
    greedyRemainderRat_transport,
    show mersenneWeightRat = Erdos257PeriodNoncollapse.mersenneWeightRat from rfl]

theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  rw [greedyRemainderRat_transport]
  exact Erdos257PeriodNoncollapse.greedyMersenneRemainderRat_half_pos n

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [cofinalPositiveHalfGreedySkips_transport,
    show mersenneAchievementSet =
      Erdos257PeriodNoncollapse.mersenneAchievementSet from rfl]
  exact Erdos257PeriodNoncollapse.cofinalPositiveHalfGreedySkips_iff_half_mem

end

end PalomarCorpus.E257.PositiveSkipEquivalence
