/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Solutions.PalomarCorpus.E68_01.CommonDenominatorGrowth

open Filter

namespace FactorialCommonDenominator

/-- The unreduced common denominator through N; the empty lcm is one. -/
def channelLCM (N : ℕ) : ℕ :=
  (Finset.Icc 2 N).lcm (fun n => n.factorial - 1)

theorem growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  simpa only [channelLCM, PalomarCorpus.E68_01.Shared.channelLCM] using
    PalomarCorpus.E68.CommonDenominatorGrowth.common_denominator_growth_liminf

end FactorialCommonDenominator

#print axioms FactorialCommonDenominator.growth_liminf
