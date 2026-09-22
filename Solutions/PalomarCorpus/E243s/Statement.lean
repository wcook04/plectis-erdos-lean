/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243s

Every non-theorem declaration of `PalomarCorpus/E243s/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter

namespace PalomarCorpus.E243.PaperStatementsS
open Filter
/-- Cumulative least common multiple of the initial denominator and all digits strictly before `n`. Local copy of ErdosProblems.Erdos243.cumulativeDigitLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.lcmDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
end PalomarCorpus.E243.PaperStatementsS
