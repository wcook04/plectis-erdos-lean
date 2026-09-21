/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249ba

Every non-theorem declaration of `PalomarCorpus/E249ba/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open ArithmeticFunction

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
/-- The quotient of the first multiple of `d` strictly above `N`. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1
/-- The least strictly positive shift from `N` to a multiple of `d` when `d > 0`. At a divisor of `N` it is `d`, rather than zero. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d
/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lambertValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)
/-- The Euler totient as an integer-valued arithmetic function. Local copy of MersenneLambertLadder.totientZ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩
/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution). `A(n)` counts the primitive Dirichlet characters of conductor `n` (OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on `n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. Local copy of MersenneLambertLadder.primWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius
end PalomarCorpus.E249.PaperStatementsBA
