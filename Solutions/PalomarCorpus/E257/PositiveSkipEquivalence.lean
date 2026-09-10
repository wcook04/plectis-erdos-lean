/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.BooleanMobiusSkipRowCofinal
import Solutions.PalomarCorpus.E257.Shared

open Set

namespace PalomarCorpus.E257.PositiveSkipEquivalence
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)

noncomputable section

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ :=
  Erdos257PeriodNoncollapse.greedyMersenneRemainderRat x

noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  change 0 < Erdos257PeriodNoncollapse.greedyMersenneRemainderRat
    (1 / 2 : ℚ) n
  exact Erdos257PeriodNoncollapse.greedyMersenneRemainderRat_half_pos n

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  change Erdos257PeriodNoncollapse.CofinalPositiveHalfGreedySkips ↔
    (1 / 2 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet
  exact Erdos257PeriodNoncollapse.cofinalPositiveHalfGreedySkips_iff_half_mem

end

end PalomarCorpus.E257.PositiveSkipEquivalence
