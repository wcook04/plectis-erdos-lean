/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68b

Every non-theorem declaration of `PalomarCorpus/E68b/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
/-- The least common multiple of the channel moduli through `D`. Local copy of Erdos68.channelLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The integer numerator of the `d`-th divisor channel. Local copy of Erdos68.channelNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- Factorial-weighted sum of a finite coefficient family. Local copy of Erdos68.factorialMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
/-- Coefficients `(p,-1)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ :=
  ![(p : ℤ), -1]
/-- Support indices `(p-1,p)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ :=
  ![p - 1, p]
/-- The exact rational prefix of the Erdős #68 series through index `n`. Local copy of ErdosProblems.Erdos68.factorialGapPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Strict successor of the factorially scaled prefix. Local copy of ErdosProblems.Erdos68.strictFacTop, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- Distance from the strict factorial successor of the preceding actual prefix to that scaled prefix. Unlike an ordinary fractional-part complement, this takes the value one when the scaled prefix is integral. Local copy of ErdosProblems.Erdos68.factorialGapPredecessorGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
/-- The exact rounding carry in the strict-successor recurrence for the Erdős #68 prefixes. Local copy of ErdosProblems.Erdos68.factorialGapStepCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
end PalomarCorpus.E68.PaperStatementsB
