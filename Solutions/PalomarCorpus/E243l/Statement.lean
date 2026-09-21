/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243l

Every non-theorem declaration of `PalomarCorpus/E243l/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
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
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.productDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243.PaperStatementsL
