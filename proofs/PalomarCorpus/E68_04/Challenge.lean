/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #68, record section 5.1: all solutions and their remainders modulo integers (part 2 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #68, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #68 remains open, and no theorem in
this entry decides it.
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
/-- States long68:res:translator from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.prime_channel_corrector in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    factorialMoment (primeTranslatorCoeff p)
      (primeTranslatorIndex p) = 0 ∧
    channelNumerator (primeTranslatorCoeff p)
      (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      channelNumerator (primeTranslatorCoeff p)
        (primeTranslatorIndex p) d = 0) := by
  sorry
end PalomarCorpus.E68.PaperStatementsB
