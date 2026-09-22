/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band h

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
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
/-- States long251:res:block from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_block_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  sorry
end PalomarCorpus.E251.PaperStatementsH
