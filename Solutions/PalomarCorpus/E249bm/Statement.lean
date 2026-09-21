/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249bm

Every non-theorem declaration of `PalomarCorpus/E249bm/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open ArithmeticFunction
open scoped BigOperators
open Finset

namespace PalomarCorpus.E249.PaperStatementsBM
open ArithmeticFunction
open scoped BigOperators
open Finset
/-- The quotient of the first multiple of `d` strictly above `N`. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1
/-- The least strictly positive shift from `N` to a multiple of `d` when `d > 0`. At a divisor of `N` it is `d`, rather than zero. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsBM
