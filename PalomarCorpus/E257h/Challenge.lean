/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band h

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E257.PaperStructuresH
/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`. `T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3` gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)` (equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). Local copy of Erdos249257.HalfGreedyFatalGap.mersenneTailLB3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by
  sorry
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.two_le_of_fatal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by
  sorry
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by
  sorry
end PalomarCorpus.E257.PaperStructuresH
