/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_02

Every non-theorem declaration of `PalomarCorpus/E243_02/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Filter Topology

namespace PalomarCorpus.E243.PaperStatementsA
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

namespace PalomarCorpus.E243.PaperStatementsH
open scoped BigOperators
end PalomarCorpus.E243.PaperStatementsH

namespace PalomarCorpus.E243.CompletePaperRecords
open Filter Topology
open scoped BigOperators
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The integer numerator obtained by clearing q times the prefix product from the first n terms of the reciprocal-series remainder. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- The natural-number projection of the cleared integer remainder numerator. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The least common multiple of q and the first n digits of a, defined recursively. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- The product of the successive gcd overlaps between each digit and the preceding cumulative least common multiple. -/
noncomputable def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)
/-- The numerator C n divided in the natural numbers by its cumulative overlap debt. -/
noncomputable def lcmLiftedNumerator (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℕ :=
  C n / cumulativeOverlapDebt q a n
/-- The signed discrepancy between the cumulative least common multiple and (a n − 1) times the lifted numerator. -/
noncomputable def lcmLiftedDigit (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℤ :=
  (cumulativeDigitLcm q a n : ℤ) -
    ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)
/-- The value at n + 1 strictly exceeds every value at an index at most n. -/
noncomputable def IsStrictRecord (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, j ≤ n → U j < U (n + 1)
/-- The integrals from 1 to R exceed every real bound as R ranges over values at least 1. -/
noncomputable def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t
/-- The overlap-corrected natural numerator of the rational reciprocal-series remainder. -/
noncomputable def canonicalLcmNumerator (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℕ :=
  lcmLiftedNumerator q a (canonicalNaturalNumerator a p q)
/-- The signed discrepancy associated with the canonical overlap-corrected numerator. -/
noncomputable def canonicalLcmDigit (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℤ :=
  lcmLiftedDigit q a (canonicalNaturalNumerator a p q)
/-- At a strict record, the negative digit excess beyond B, weighted by f at the preceding numerator; zero at other indices. -/
noncomputable def paperRecordCharge (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if IsStrictRecord U n then
    ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) * f (U n : ℝ)
  else 0
end PalomarCorpus.E243.CompletePaperRecords
