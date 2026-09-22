/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfGreedyFatalGap
import Solutions.PalomarCorpus.E257h.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresH

theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := @Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd k u L a hk hu ha hodd hdecomp T hT hfatal

theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := @Erdos249257.HalfGreedyFatalGap.two_le_of_fatal k u L a hk hu ha hdecomp T hT hfatal

theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by
  apply Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe <;> assumption

end PalomarCorpus.E257.PaperStructuresH
