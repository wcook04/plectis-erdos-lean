/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfGreedyFatalGap
import Solutions.PalomarCorpus.E257v.Statement

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresV

theorem unitNumerator_skipSafe_actualTail {k u L a : ℕ}
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k := by
  apply Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe_actualTail <;> assumption

end PalomarCorpus.E257.PaperStructuresV
