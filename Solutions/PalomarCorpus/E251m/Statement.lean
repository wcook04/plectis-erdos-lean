/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251m

Every non-theorem declaration of `PalomarCorpus/E251m/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsM
open scoped BigOperators
/-- A bound is dyadically dominated when every fixed rational denominator is eventually overwhelmed by the depth scale. Polynomial bounds have this property; the definition isolates exactly the growth input used below. Local copy of ErdosProblems.Erdos251.DyadicScaleDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ,
    2 * bound (N + r) * q < 2 ^ r
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- `x` lies in the affine class `-c` modulo `2^(r+1)`. Local copy of ErdosProblems.Erdos251.RatAffinePowTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)
/-- A rational that is the cast of an even integer. Local copy of ErdosProblems.Erdos251.RatEvenIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatEvenIntegral (x : ℚ) : Prop := ∃ k : ℤ, x = ((2 * k : ℤ) : ℚ)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The integer block accumulated through `h` dyadic tail steps beginning at index `N`. Recursively, this is `g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. Local copy of ErdosProblems.Erdos251.dyadicTailBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)
/-- The least common multiple of the positive integers seen so far. Local copy of ErdosProblems.Erdos251.lcmDiagonalSchedule, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- The digit sequence governing the fixed `h`-shift cocycle. Local copy of ErdosProblems.Erdos251.shiftDigit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251.PaperStatementsM
