/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257h

Every non-theorem declaration of `PalomarCorpus/E257h/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E257.PaperStructuresH
/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`. `T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3` gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)` (equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). Local copy of Erdos249257.HalfGreedyFatalGap.mersenneTailLB3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)
end PalomarCorpus.E257.PaperStructuresH
