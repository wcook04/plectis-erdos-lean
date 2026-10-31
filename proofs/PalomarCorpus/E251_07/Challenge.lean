/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, the lcm diagonal criterion, polynomial shift countermodel and prime gap identity families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
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
/-- The complementary form: for every real orbit obeying the dyadic tail recurrence with integer digits, `T 0` is irrational exactly when for every positive shift length and every threshold some later index has a non-integral shift. -/
theorem irrationalInitial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T := by
  sorry
/-- For a rational orbit obeying the dyadic tail recurrence with integer digits, the shift `T (N + h) - T N` is an integer exactly when the multiplicative order of 2 in the integers modulo the reduced denominator of `T N` divides `h`. When that denominator is even, 2 is not a unit and no positive power of 2 equals 1, so `orderOf` takes the Mathlib value 0 for an element of infinite order and only `h = 0` divides it, matching the fact that no positive shift at such a basepoint is integral. -/
theorem tailShiftIntegral_iff_orderOf_dvd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      orderOf (2 : ZMod (T N).den) ∣ h := by
  sorry
/-- Hypotheses: `T` is a real orbit obeying the dyadic tail recurrence with integer digits, and the natural-valued sequence `s` is everywhere positive, is eventually divisible by every fixed positive shift length, and is eventually at least every fixed index. Conclusion: `T 0` is irrational exactly when `T (s j + s j) - T (s j)` fails to be an integer for every `j`, so a single diagonal sequence decides irrationality. -/
theorem irrationalInitial_iff_nonintegral_on_schedule
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) := by
  sorry
/-- Specialisation of the schedule criterion to the least common multiples: a real orbit obeying the dyadic tail recurrence with integer digits has irrational initial value exactly when, at every index `j`, the shift of length `lcm (1, ..., j)` taken at the basepoint `lcm (1, ..., j)` fails to be an integer. -/
theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  sorry
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
/-- The quadratic word `a n = 2 * (n ^ 2 + 4 * n + 2)` and the orbit `U n = 2 * (n + 4) ^ 2` satisfy the dyadic tail recurrence; the word is positive, even and strictly increasing, hence unbounded and not eventually periodic; every shift `U (N + h) - U N` is an integer; every adjacent difference `a (n + 1) - a n` equals `4 * n + 10` and is therefore never 2 and never -2; and the series sums to the rational number 32, so it fails to be irrational. Those coarse properties are jointly compatible with a rational value. The word is synthetic and is not the prime-gap word. -/
theorem polynomialGapTailCountermodel :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
      (∀ n, 0 < polynomialGapWord n) ∧
      (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
      StrictMono polynomialGapWord ∧
      (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
      (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ)) ∧
      (∀ n,
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
      (∑' n : ℕ, polynomialGapDyadicTerm n) = 32 ∧
      ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by
  sorry
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
/-- Unconditional elementary bound: the `(n + 1)`st prime is at most `1250 * (n + 1) ^ 4`. It is proved from a central binomial estimate for the prime counting function and supplies the convergence used in this family without the prime number theorem. -/
theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 := by
  sorry
/-- The normalised prime dyadic series with terms `prime0 n / 2 ^ (n + 1)` is summable, by the polynomial prime bound. -/
theorem primeSeries_summable : Summable primeDyadicTerm := by
  sorry
/-- The consecutive-prime-gap dyadic series with terms `primeGap0 n / 2 ^ (n + 1)` is summable. -/
theorem primeGapSeries_summable : Summable primeGapDyadicTerm := by
  sorry
/-- Exact unconditional identity from summation by parts over the dyadic weights: the sum over `n` of `prime0 n / 2 ^ (n + 1)` equals `2` plus the sum over `n` of `primeGap0 n / 2 ^ (n + 1)`. -/
theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry
/-- Exact reformulation: the normalised prime dyadic series is irrational exactly when the consecutive-prime-gap dyadic series is irrational, because the two differ by the integer 2. The equivalence changes coordinates and decides neither value. -/
theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry
/-- Exact unconditional identity in the displayed indexing: the sum over `n` of `prime0 n / 2 ^ n` equals `4` plus twice the sum over `n` of `primeGap0 n / 2 ^ (n + 1)`. -/
theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry
/-- Exact reformulation: the displayed prime series with denominators `2 ^ n` is irrational exactly when the consecutive-prime-gap series is irrational, because the two differ by a rational affine change of variable. The equivalence decides neither value. -/
theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry
end PalomarCorpus.E251.PrimeGapIdentity

namespace PalomarCorpus.E251.PrimeGapNonperiodicity
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251_07.Shared (prime0 primeGap0)
/-- The consecutive prime-gap sequence is not eventually periodic with any positive period. -/
theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  sorry
end PalomarCorpus.E251.PrimeGapNonperiodicity
