/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_07

Every non-theorem declaration of `PalomarCorpus/E243_07/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243_07.Shared
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The denominator q multiplied by the product of the first n terms of a. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The canonical centred error `E_n = D_n - (a_n - 1) C_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.canonicalError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalError (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℤ)
/-- The correction term `Λ_n` of `long243:eq:shiftedsign`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext
/-- `Λ_n` on the canonical orbit. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCorrection (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℝ :=
  shiftedCorrectionTerm (a n : ℝ) (a (n + 1) : ℝ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
    ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)
    ((canonicalError a p q n : ℤ) : ℝ) ((canonicalError a p q (n + 1) : ℤ) : ℝ)
end PalomarCorpus.E243_07.Shared

namespace PalomarCorpus.E243.PaperStatementsE
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (shiftedCorrectionTerm)
end PalomarCorpus.E243.PaperStatementsE

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (canonicalCorrection canonicalDenominator canonicalError canonicalNaturalNumerator centeredState clearedIntegerNumerator prefixProduct shiftedCorrectionTerm)
end PalomarCorpus.E243.PaperStatementsL

namespace PalomarCorpus.E243.PaperStatementsQ
open Filter
open scoped BigOperators
export PalomarCorpus.E243_07.Shared (canonicalCorrection canonicalDenominator canonicalError canonicalNaturalNumerator centeredState clearedIntegerNumerator prefixProduct shiftedCorrectionTerm)
/-- Cumulative least common multiple of the initial denominator and all digits strictly before `n`. Local copy of ErdosProblems.Erdos243.cumulativeDigitLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- The Erdős-Straus quantity `Z_n^ES = ([a_0,…,a_n]/a_{n+1})(a_{n+1}²/a_{n+2} - 1)`. The least common multiple is the `q = 1` cumulative one: it includes `a_n` and not the clearing denominator. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosStrausQuantity (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a (n + 1) : ℝ) / (a (n + 1) : ℝ) *
    ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1)
/-- The LCM-cleared numerator `U_n = L_n x_n`. It is an integer because `q ∣ L_n` and `a_j ∣ L_n` for every `j < n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.lcmClearedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmClearedNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * ((cumulativeDigitLcm q a n / q : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, ((cumulativeDigitLcm q a n / a j : ℕ) : ℤ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.productDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- Cumulative product of the irreversible LCM-overlap payments. Local copy of ErdosProblems.Erdos243.cumulativeOverlapDebt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)
/-- Product-cleared denominator scale through the first `n` digits. Local copy of ErdosProblems.Erdos243.digitProductScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digitProductScale (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * digitProductScale q a n
end PalomarCorpus.E243.PaperStatementsQ

namespace PalomarCorpus.E243.PaperStatementsD
open Filter
open scoped BigOperators
open scoped Topology
/-- `ℓ x = log₂ log₂ max(4, x)`, the scale of the long #243 note. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.ellScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ellScale (x : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (max 4 x))
end PalomarCorpus.E243.PaperStatementsD

namespace PalomarCorpus.E243.PaperStatementsA
end PalomarCorpus.E243.PaperStatementsA
