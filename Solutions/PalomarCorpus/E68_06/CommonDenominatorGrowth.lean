/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteLiminf
import Solutions.PalomarCorpus.E68_06.Statement

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.CommonDenominatorGrowth
export PalomarCorpus.E68_06.Shared (channelLCM)

theorem common_denominator_growth :
    LowerLimitAtLeast
      (fun N : ℕ => Real.log (channelLCM N : ℝ) /
        ((N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)))
      (2 * Real.sqrt 2 / 3) := by
  simpa only [LowerLimitAtLeast,
    ErdosProblems.Erdos68.PaperComplete.LowerLimitAtLeast,
    channelLCM, _root_.Erdos68.channelLCM] using
    ErdosProblems.Erdos68.PaperComplete.common_denominator_growth

theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  simpa only [channelLCM, _root_.Erdos68.channelLCM] using
    ErdosProblems.Erdos68.PaperComplete.common_denominator_growth_liminf

theorem asymptotic_radius_constant_liminf (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    (((16 : ℝ) / 9) : EReal) ≤
      Filter.liminf (fun t : ℕ =>
        ((((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 : ℝ) : EReal)) atTop := by
  refine ErdosProblems.Erdos68.PaperComplete.asymptotic_radius_constant_liminf M R ?_
  simpa only [channelLCM, _root_.Erdos68.channelLCM] using hH

end PalomarCorpus.E68.CommonDenominatorGrowth
