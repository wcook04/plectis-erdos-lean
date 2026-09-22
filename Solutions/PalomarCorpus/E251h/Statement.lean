/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251h

Every non-theorem declaration of `PalomarCorpus/E251h/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsH
open scoped BigOperators
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- The integer block accumulated through `h` dyadic tail steps beginning at index `N`. Recursively, this is `g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. Local copy of ErdosProblems.Erdos251.dyadicTailBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
end PalomarCorpus.E251.PaperStatementsH
