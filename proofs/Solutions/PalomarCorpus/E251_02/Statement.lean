/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251_02

Every non-theorem declaration of `PalomarCorpus/E251_02/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Filter
open Topology
open Finset
open Filter Topology

namespace PalomarCorpus.E251_02.Shared
/-- The same dyadic tail recurrence with integer digits `g` for a real sequence: `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the reals. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it equals the cast of an integer. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The term of the normalised prime dyadic series: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ (n + 1)`. The sum over `n` at least 0 is `2/2 + 3/4 + 5/8` and so on, the value whose irrationality Erdős problem 251 asks about. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- The term of the consecutive-prime-gap dyadic series: the `n`th prime gap, cast to a real number, divided by `2 ^ (n + 1)`. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- The exact rational partial sum of the first `n` terms of the prime-gap dyadic series, the finite sum over `i` in `Finset.range n` of `primeGap0 i / 2 ^ (i + 1)` computed in the rationals. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- The genuine scaled tail after the first `N+1` prime-gap terms. Local copy of ErdosProblems.Erdos251.realPrimeGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
end PalomarCorpus.E251_02.Shared

namespace PalomarCorpus.E251.PaperStatementsL
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail)
/-- **(P)**: for every positive modulus and every cutoff, some pair of indices beyond the cutoff, congruent modulo the modulus, has a nonintegral tail difference. Local copy of ErdosProblems.Erdos251.CofinalFreePairNonintegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)
end PalomarCorpus.E251.PaperStatementsL

namespace PalomarCorpus.E251.PaperStatementsM
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealDyadicTailRecurrence RealIntegral realTailShift)
/-- The least common multiple of the positive integers seen so far. Local copy of ErdosProblems.Erdos251.lcmDiagonalSchedule, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
end PalomarCorpus.E251.PaperStatementsM

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealDyadicTailRecurrence RealIntegral prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251.PaperStatementsG

namespace PalomarCorpus.E251.PaperStatementsO
open Filter
open Topology
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
/-- Real quartic from the displayed remainder, with all constants unchanged. Local copy of ErdosProblems.Erdos251.PaperR7.quarticTailPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarticTailPolynomial (x : ℝ) : ℝ :=
  x ^ 4 + 8 * x ^ 3 + 36 * x ^ 2 + 104 * x + 150
/-- Local copy of ErdosProblems.Erdos251.PaperR7.explicitRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def explicitRemainder (h N L : ℕ) : ℝ :=
  1250 / 2 ^ L * (quarticTailPolynomial ((N : ℝ) + h + L + 2) +
    quarticTailPolynomial ((N : ℝ) + L + 2))
/-- Euclidean distance to the complete integer lattice. Local copy of ErdosProblems.Erdos251.PaperR7.integerDistance, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))
/-- Local copy of ErdosProblems.Erdos251.PaperR7.signedWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)
end PalomarCorpus.E251.PaperStatementsO

namespace PalomarCorpus.E251.PaperStatementsP
open scoped BigOperators
open Finset
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
end PalomarCorpus.E251.PaperStatementsP

namespace PalomarCorpus.E251.PaperStatementsB
open Filter
open Topology
end PalomarCorpus.E251.PaperStatementsB

namespace PalomarCorpus.E251.ExactDenominatorFloors
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
end PalomarCorpus.E251.ExactDenominatorFloors

namespace PalomarCorpus.E251.PaperStatementsF
open scoped BigOperators
open Finset
end PalomarCorpus.E251.PaperStatementsF
