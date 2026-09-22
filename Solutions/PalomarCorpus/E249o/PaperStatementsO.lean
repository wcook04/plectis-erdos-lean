/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.SignedQMomentObstruction
import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import ErdosProblems.Erdos249.PaperCompleteR7.ShortNoteAssemblies
import ErdosProblems.Erdos249.RankOneSubrankObstruction
import Solutions.PalomarCorpus.E249o.Statement

open scoped BigOperators
open Matrix
open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsO

theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r := @ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersennePrefix_eq_icc_sum Y r

theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584 := @ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates r Y hr hY

theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := @ErdosProblems.Erdos249.PaperCompleteR7.rankOne_denominator_pos e Y he hY

end PalomarCorpus.E249.PaperStatementsO
