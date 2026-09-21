/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243a

Every non-theorem declaration of `PalomarCorpus/E243a/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E243.PaperStatementsA
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card
/-- Arbitrarily late prefixes have arbitrarily small exceptional proportion. The strict inequality automatically excludes the zero-length prefix. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.ZeroLowerDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)
/-- The literal unshifted polynomial printed as Q_{m,c} in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.rationalBinomialCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c
/-- Integer-valued binomial basis for a rising cubic. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.risingBinomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)
/-- Index set of the barrier family: `k` indexes the barrier `(2 * k + 1) * p` lying in the window `(p * Q / 4, p * Q / 2]`. Local copy of ErdosProblems.Erdos243.barrierIdx, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def barrierIdx (Q : ℕ) : Finset ℕ := Finset.Icc ((Q + 4) / 8) ((Q - 2) / 4)
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. Local copy of ErdosProblems.Erdos243.nextDenState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. Local copy of ErdosProblems.Erdos243.nextTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- The next denominator defect from the Sylvester step. Local copy of ErdosProblems.Erdos243.sylvesterDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a
end PalomarCorpus.E243.PaperStatementsA
