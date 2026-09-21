/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249al

Every non-theorem declaration of `PalomarCorpus/E249al/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Classical

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- **The paper's binary example.** Reading the expansion two digits at a time, the block with index `k ≥ 1` is `10` when `k` is a perfect square and `01` otherwise. Position `n` sits inside the block with index `n / 2 + 1`, and is that block's first digit exactly when `n` is even. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0
/-- The real number whose binary digits, read from position `n` on, are `d n, d (n+1), d (n+2), …`. For `n = 0` this is the number itself; for general `n` it is the tail left after `n` binary shifts. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)
/-- **ξ**, the number of the paper's binary example. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := tail digit 0
end PalomarCorpus.E249.PaperStatementsAL
