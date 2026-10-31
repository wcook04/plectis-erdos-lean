/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251_07

Every non-theorem declaration of `PalomarCorpus/E251_07/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Topology
open scoped BigOperators

namespace PalomarCorpus.E251_07.Shared
/-- The dyadic tail recurrence with integer digits `g`: a rational sequence `T` satisfies `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the rationals. This is the relation obeyed by the rescaled tails `T N = sum over j at least 1 of g (N + j) / 2 ^ j` of a dyadic series with integer coefficients. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the image of an integer under the cast from the integers to the rationals, equivalently when its reduced denominator is 1. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251_07.Shared

namespace PalomarCorpus.E251.LcmDiagonalCriterion
export PalomarCorpus.E251_07.Shared (DyadicTailRecurrence RatIntegral tailShift)
/-- The same dyadic tail recurrence with integer digits `g` for a real sequence: `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the reals. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- A real number is integral when it equals the cast of an integer. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The cofinal non-integrality criterion used by this family: for every positive shift length `h` and every threshold `N₀` some index `N` at least `N₀` has `T (N + h) - T N` not an integer. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬ RealIntegral (realTailShift T h N)
/-- The schedule with value 1 at index 0 and `lcm (value at j) (j + 1)` at index `j + 1`, so that its value at `j` is the least common multiple of the integers from 1 to `j`. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
end PalomarCorpus.E251.LcmDiagonalCriterion

namespace PalomarCorpus.E251.PolynomialShiftCountermodel
export PalomarCorpus.E251_07.Shared (DyadicTailRecurrence RatIntegral tailShift)
/-- The explicit rational orbit `U n = 2 * (n + 4) ^ 2` of the quadratic countermodel, computed in the natural numbers and cast to the rationals. -/
noncomputable def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)
/-- The explicit quadratic digit word `a n = 2 * (n ^ 2 + 4 * n + 2)`, a positive even strictly increasing sequence of integers. This is a synthetic model word and it is not the consecutive-prime-gap sequence. -/
noncomputable def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)
/-- The real term of the countermodel series, indexed so that index `n` carries the digit `a (n + 1)` divided by `2 ^ (n + 1)`. The digit at index 0 is the initial carry and does not appear in the series. -/
noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)
end PalomarCorpus.E251.PolynomialShiftCountermodel

namespace PalomarCorpus.E251.PrimeGapIdentity
export PalomarCorpus.E251_07.Shared (prime0 primeGap0)
/-- The term of the normalised prime dyadic series: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ (n + 1)`. The sum over `n` at least 0 is `2/2 + 3/4 + 5/8` and so on, the value whose irrationality Erdős problem 251 asks about. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- The term of the displayed prime series with denominator `2 ^ n`: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ n`, so that the sum is `2 + 3/2 + 5/4` and so on, twice the normalised series. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
/-- The term of the consecutive-prime-gap dyadic series: the `n`th prime gap, cast to a real number, divided by `2 ^ (n + 1)`. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
end PalomarCorpus.E251.PrimeGapIdentity

namespace PalomarCorpus.E251.PrimeGapNonperiodicity
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251_07.Shared (prime0 primeGap0)
end PalomarCorpus.E251.PrimeGapNonperiodicity
