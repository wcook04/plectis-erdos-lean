/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257af

Every non-theorem declaration of `PalomarCorpus/E257af/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
/-- Completely explicit constant for the fixed-`k` divisor bound. Local copy of Erdos249257.divisorSubpowerConst, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)
/-- Numerator left after subtracting a reduced finite prefix `r / D` from a dyadic rational `p / 2^c`. The transport theorem below assumes the subtraction is nonnegative, so natural subtraction is exact. Local copy of Erdos249257.dyadicResidualNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r
/-- The displayed residual rational before its remaining power-of-two cancellation is normalized by `Rat`. Local copy of Erdos249257.dyadicResidualRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)
/-- For a displayed residual `p / (2L)`, the integer numerator of its excess above the next dyadic point `2^-(n+1)`. Indeed, `p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`. Keeping `E` integral makes the unresolved skipped-branch comparison an exact Diophantine inequality rather than a real-valued phase estimate. Local copy of Erdos249257.nextDyadicExcessIntNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)
end PalomarCorpus.E257.PaperStatementsAF
