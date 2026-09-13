/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.BooleanMobiusSkipRowCofinal
import Solutions.PalomarCorpus.E257.Statement

open Set

namespace PalomarCorpus.E257.PositiveSkipEquivalence
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)

noncomputable section

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
