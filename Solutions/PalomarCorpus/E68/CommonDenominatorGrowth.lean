/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteLiminf
import Solutions.PalomarCorpus.E68.Shared

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.CommonDenominatorGrowth
export PalomarCorpus.E68.Shared (channelLCM)

noncomputable def LowerLimitAtLeast (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ n : ℕ in atTop, a < f n

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

end PalomarCorpus.E68.CommonDenominatorGrowth
