/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.RankOneSharpFloor
import Solutions.PalomarCorpus.E249.Statement

open Filter Topology
open scoped BigOperators
open ArithmeticFunction

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E249.RankOneDenominator
export PalomarCorpus.E249.Shared (mobiusMersennePrefix mobiusMersenneTerm)

theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  simpa only [mobiusMersennePrefix, mobiusMersenneTerm, ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOne_denominator_pos he hY

end PalomarCorpus.E249.RankOneDenominator
end
