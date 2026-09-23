/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_04

Every non-theorem declaration of `PalomarCorpus/E68_04/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
/-- The integer numerator of the `d`-th divisor channel. Local copy of Erdos68.channelNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)
/-- Factorial-weighted sum of a finite coefficient family. Local copy of Erdos68.factorialMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
/-- Coefficients `(p,-1)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ :=
  ![(p : ℤ), -1]
/-- Support indices `(p-1,p)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ :=
  ![p - 1, p]
end PalomarCorpus.E68.PaperStatementsB
