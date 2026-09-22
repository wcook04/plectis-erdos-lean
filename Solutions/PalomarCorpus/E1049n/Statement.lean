/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049n

Every non-theorem declaration of `PalomarCorpus/E1049n/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
/-- Cyclotomic denominator-saving expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpCyclotomicSaving, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- Quadratic Archimedean decay expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpDecay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- Homogeneous polynomial-width expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- Rational-base height threshold associated with the explicit exponent model above. Local copy of ErdosProblems.Erdos1049.hpThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
/-- Twice the proposed common denominator exponent `Eₙ = (3n² - n) / 2`. Local copy of ErdosProblems.Erdos1049.rationalPadeDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n
/-- The real error of an integer Padé coefficient pair `(U,V)` at `S`. Local copy of ErdosProblems.Erdos1049.rationalPadeError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeError (S : ℝ) (U V : ℤ) : ℝ :=
  (U : ℝ) * S - (V : ℝ)
/-- The exterior determinant of two integer Padé coefficient pairs. For the adjacent Zudilin construction this is `Uₙ Vₘ - Uₘ Vₙ`. Unlike either individual coefficient pair, the determinant can inherit every divisor common to the two `U` coefficients and every divisor common to the two `V` coefficients. Local copy of ErdosProblems.Erdos1049.rationalPadeExteriorDet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeExteriorDet (Un Vn Um Vm : ℤ) : ℤ :=
  Un * Vm - Um * Vn
/-- Twice the denominator exponent of the `k`-th summand in the homogenised little-`q` Legendre `P` polynomial. Local copy of ErdosProblems.Erdos1049.rationalPadePSummandDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)
/-- Twice the maximal denominator exponent in the `Q`-summand calculation, after the change of variables `j = n - m - 1`. Local copy of ErdosProblems.Erdos1049.rationalPadeQMaxDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m
end PalomarCorpus.E1049.PaperStatementsN
