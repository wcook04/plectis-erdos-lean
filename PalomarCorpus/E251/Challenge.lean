/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251

Erdős asked whether the dyadic prime series `2/2 + 3/4 + 5/8` and so on is
irrational. Write `p n` for the primes indexed from `p 0 = 2`, so that the
series is `sum p n / 2 ^ (n + 1)`, and `g n = p (n + 1) - p n` for the
consecutive gaps. The parent problem remains open, and no declaration
in this module asserts irrationality of any series.

## What is stated here

* **Shifted four-prime counting.** For `h` at least 2 and any integer `r`, a
  finite unconditional inequality bounds the number of indices `n < N` with
  `g (n + h) - g n = r` by an explicit separated four-prime candidate count
  plus a large-span term (`shifted_count_bound`, no sieve assumption). Under
  the explicit unproved hypothesis `SeparatedQuadSieve_target`, those
  coincidences have density zero (`separated_zeroDensity_of_quad_sieve`).
  This module does not prove that sieve estimate.
* **Exact reformulations.** `p n <= 1250 (n + 1) ^ 4` gives unconditional
  summability; summation by parts gives
  `sum p n / 2 ^ (n + 1) = 2 + sum g n / 2 ^ (n + 1)` and
  `sum p n / 2 ^ n = 4 + 2 sum g n / 2 ^ (n + 1)`, with the matching
  irrationality equivalences. The identity was given by Terence Tao on the
  public problem thread on 7 October 2025 and carries no priority claim here.
* **Tail-shift criteria.** For the recurrence `T (N + 1) = 2 T N - g (N + 1)`
  with arbitrary integer digits, irrationality of `T 0` is equivalent to
  cofinal non-integrality of every fixed positive shift, to the free-pair
  condition with free offset, and to non-integrality on the lcm diagonal. Two
  proposed escape tests are proved equivalent to that same conclusion.
* **Denominator floor.** Every rational `a / b` equal to either series has `b`
  at least `2 ^ 589`, decided inside the Lean kernel from a trial-division
  sieve to `10 ^ 4` and a Farey certificate. This finite exclusion is
  compatible with rationality.
* **Synthetic countermodels.** An every-residue logarithmic word and the
  quadratic word `2 (n ^ 2 + 4 n + 2)` have rational dyadic sums `6` and `32`
  while carrying long lists of coarse gap properties. Neither word is the
  prime-gap word and neither asserts that any position is prime.
* **Sparse rationalisation.** For any natural digit word `a` with convergent
  dyadic sum `A` and any envelope tending to infinity, one support set of upper
  Banach density zero and one interval `[l, u]` above `A` are fixed such that
  every real in the interval is the dyadic sum of `a + e` for a word `e` on
  that support, bounded by the envelope and eventually divisible, with its
  prefix sums, by every positive modulus. With the envelope `(log (n + 3)) ^ ε`
  the support count is `O(X / log log X)`, and adding `e` moves block
  statistics of length `o(log log X)` by a total variation tending to `0`.
  The word is arbitrary, and no statement here concerns the prime digits.
-/

open scoped BigOperators
open Filter
open scoped BigOperators Topology
open Finset
open Filter Topology

namespace PalomarCorpus.E251.Shared
/-- The dyadic tail recurrence with integer digits `g`: a rational sequence `T` satisfies `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the rationals. This is the relation obeyed by the rescaled tails `T N = sum over j at least 1 of g (N + j) / 2 ^ j` of a dyadic series with integer coefficients. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the image of an integer under the cast from the integers to the rationals, equivalently when its reduced denominator is 1. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- The same dyadic tail recurrence with integer digits `g` for a real sequence: `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the reals. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it equals the cast of an integer. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- Uniformly in the starting index, every sufficiently long interval contains at most a 1/R proportion of S, for each positive integer R. -/
noncomputable def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L
/-- The starting indices in I whose length-m block lies in the specified event. -/
noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)
/-- The smoothed iterated logarithm log(log(n + 3)). -/
noncomputable def iterlog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 3))
/-- The envelope (log(n + 3))^α. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
/-- The term of the normalised prime dyadic series: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ (n + 1)`. The sum over `n` at least 0 is `2/2 + 3/4 + 5/8` and so on, the value whose irrationality Erdős problem 251 asks about. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
/-- The term of the consecutive-prime-gap dyadic series: the `n`th prime gap, cast to a real number, divided by `2 ^ (n + 1)`. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- The shift of length `h` at basepoint `N` of a rational orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251.Shared

namespace PalomarCorpus.E251.ActualPrimeGapTail
open scoped BigOperators
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral prime0 primeGap0 primeGapDyadicTerm tailShift)
/-- The exact rational partial sum of the first `n` terms of the prime-gap dyadic series, the finite sum over `i` in `Finset.range n` of `primeGap0 i / 2 ^ (i + 1)` computed in the rationals. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- For a rational number `S`, the rational state `2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))`, which is the rescaled tail that `S` would have at index `N` if `S` were the value of the prime-gap dyadic series. It is defined for every rational `S`, with no hypothesis that `S` is that value. -/
noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ :=
  2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))
/-- Hypothesis: the sum of the prime-gap dyadic series fails to be irrational. Conclusion: some rational `S` has real cast equal to that sum, and at every index `N` the cast of `rationalPrimeGapTailState S N` equals `2 ^ (N + 1)` times the sum over `k` of the series terms from index `N + 1` onwards. The conclusion identifies the algebraic states with the actual scaled real tails and asserts nothing about irrationality. -/
theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  sorry
/-- For every rational `S`, with no rationality hypothesis on the series, the states `rationalPrimeGapTailState S` satisfy the dyadic tail recurrence whose digits are the actual consecutive prime gaps cast into the integers, that is `T (N + 1) = 2 * T N - g (N + 1)` at every index. -/
theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) := by
  sorry
/-- For every rational `S` there exist a positive shift length `h` and a threshold `N₀` such that `tailShift (rationalPrimeGapTailState S) h N` is an integer at every index `N` at least `N₀`. The shift length is produced by decomposing the denominator of `S` and is not known in advance for the prime-gap series. -/
theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) := by
  sorry
/-- For every rational `S` there exists a positive shift length `h` for which no threshold makes `tailShift (rationalPrimeGapTailState S) h N` lie strictly between -1 and 1 at every later index; non-periodicity of the actual prime gaps drives the denominator-selected integral shift out of the open unit interval infinitely often. The conclusion is compatible with rationality of the series and proves no irrationality. -/
theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 := by
  sorry
end PalomarCorpus.E251.ActualPrimeGapTail

namespace PalomarCorpus.E251.AffineCircularity
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)
/-- The weighted integer block of the `r` digits following index `N`, defined by value 0 at depth 0 and `2 * (value at depth r) + g (N + r + 1)` at depth `r + 1`, so that the value at depth `r` is `2 ^ (r - 1) * g (N + 1) + ... + g (N + r)`. Iterating the dyadic tail recurrence `r` times subtracts exactly this integer. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | r + 1 => 2 * dyadicTailBlock g N r + g (N + r + 1)
/-- The data-dependent affine condition at depth `r`: the rational `x` is the cast of an integer of the form `2 ^ (r + 1) * z - c`, that is `x` lies in the coset of `-c` modulo `2 ^ (r + 1)` inside the integers. -/
noncomputable def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)
/-- The difference digit at offset `h`, the integer `g (n + h) - g n`. This is the digit sequence obeyed by the shift `T (N + h) - T N` of an orbit whose digits are `g`. -/
noncomputable def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n
/-- A rational bounding sequence is dyadically dominated when for every basepoint `N` and every positive integer `q` some depth `r` satisfies `2 * bound (N + r) * q < 2 ^ r`, so that doubling at depth `r` outruns the bound against any fixed denominator `q`. -/
noncomputable def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ, 2 * bound (N + r) * q < 2 ^ r
/-- Exact normal form for the adjacent unit-window event. Hypotheses: the rational orbit `T` obeys the dyadic tail recurrence with integer digits `g`, and `g (N + h + 1) - g (N + 1)` is even. Conclusion: the conjunction that both shifts `T (N + h) - T N` and `T (N + h + 1) - T (N + 1)` lie strictly between -1 and 1 while `g (N + h + 1)` differs from `g (N + 1)` holds exactly when either the digit difference is 2 and the shift at `N` lies strictly between 1/2 and 1, or the digit difference is -2 and the shift at `N` lies strictly between -1 and -1/2. -/
theorem adjacent_small_mismatch_iff_signed_two_window
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧
        -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧
        g (N + h + 1) ≠ g (N + 1)) ↔
      ((g (N + h + 1) - g (N + 1) = 2 ∧
          1 / 2 < tailShift T h N ∧ tailShift T h N < 1) ∨
        (g (N + h + 1) - g (N + 1) = -2 ∧
          -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) := by
  sorry
/-- Route closure for the affine cylinder test. Hypotheses: the rational orbit `T` obeys the dyadic tail recurrence with integer digits `g`, the offset `h` is fixed, and every difference `g (N + h + 1) - g (N + 1)` is even. Conclusion: cofinal failure of the affine condition, meaning that beyond every threshold some index `N` and depth `r` have `tailShift T h (N + r)` outside the coset determined by the observed difference block, is equivalent to the shift of length `h` failing to be eventually integral. The test therefore carries no information beyond the conclusion it was introduced to supply. -/
theorem cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  sorry
/-- Route closure for the fixed-lattice test. Hypotheses: the rational orbit `T` obeys the dyadic tail recurrence with integer digits `g`, the offset `h` is fixed, and a rational sequence `bound` satisfies `|tailShift T h N| <= bound N` at every `N` and is dyadically dominated. Conclusion: cofinal separation of the observed difference block from every multiple of `2 ^ r` by more than `bound (N + r)` is equivalent to the shift of length `h` failing to be eventually integral. -/
theorem cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (bound : ℕ → ℚ)
    (hbound : ∀ N, |tailShift T h N| ≤ bound N)
    (hscale : DyadicScaleDominates bound) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
      ∀ z : ℤ, bound (N + r) <
        |((dyadicTailBlock (shiftDigit g h) N r : ℤ) : ℚ) -
          2 ^ r * (z : ℚ)|) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  sorry
end PalomarCorpus.E251.AffineCircularity

namespace PalomarCorpus.E251.AllResidueLogarithmicCountermodel
open Filter
open scoped BigOperators Topology
/-- Synthetic countermodel: there are integer sequences `digit`, `carry` and `position` with `position n = 3 + digit 1 + ... + digit n`, every digit from index 1 positive and even, values 2 and 4 both occurring beyond every cutoff in every residue class modulo every positive `t`, unbounded digits, no positive eventual period, the bound `digit n <= 4 * log (n + 1) + 24`, strictly increasing odd positions, `position N / (N * log N)` tending to 1, every scaled tail `sum over j at least 0 of digit (N + j + 1) / 2 ^ (j + 1)` summing to the integer `carry N`, that sum being 6 at `N = 0`, and every difference of two tails an integer. The digits are not the prime gaps and no position is asserted prime. -/
theorem exists_every_residue_logarithmic_countermodel :
    ∃ digit carry position : ℕ → ℤ,
    (∀ n, position n = 3 + ∑ j ∈ Finset.range n, digit (j + 1)) ∧
    (∀ n, 1 ≤ n → 0 < digit n ∧ (2 : ℤ) ∣ digit n) ∧
    (∀ t r : ℕ, 0 < t → r < t → ∀ N : ℕ,
      ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ i % t = r ∧ j % t = r ∧ digit i = 2 ∧ digit j = 4) ∧
    (∀ B₀ : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B₀ < digit n) ∧
    (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n) ∧
    (∀ n : ℕ, (digit n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 1) + 24) ∧
    StrictMono position ∧ (∀ n, ∃ z : ℤ, position n = 2 * z + 1) ∧
    HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
    (∀ N : ℕ, HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ)) ∧
    (∀ N h : ℕ, ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
    Tendsto (fun N : ℕ => (position N : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.AllResidueLogarithmicCountermodel

namespace PalomarCorpus.E251.ExactDenominatorFloors
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
/-- Any positive denominator representing either the dyadic prime series or the dyadic prime-gap series is at least 2^589 and strictly exceeds 10^177. -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) := by
  sorry
end PalomarCorpus.E251.ExactDenominatorFloors

namespace PalomarCorpus.E251.FreePairEquivalence
open scoped BigOperators
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral prime0 primeGap0 primeGapDyadicTerm realTailShift)
/-- The fixed-offset cofinal criterion for a real orbit: for every positive shift length `h` and every threshold `N₀` there is an index `N` at least `N₀` at which `T (N + h) - T N` fails to be an integer. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
/-- The free-pair criterion for a real orbit: for every positive modulus `t` and every threshold `N₀` there are indices `N` and `M` at least `N₀` which are congruent modulo `t` and have `T M - T N` not an integer. The offset `M - N` is not fixed in advance. -/
noncomputable def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)
/-- The complete scaled real tail of the prime-gap dyadic series after the first `N + 1` gaps: `2 ^ (N + 1)` times the sum over `k` of the series terms from index `N + 1` onwards, which equals the sum over `j` at least 1 of `g (N + j) / 2 ^ j`. -/
noncomputable def primeGapRealTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1))
/-- Erdős problem 251 in free-pair form: the consecutive-prime-gap dyadic series is irrational exactly when its complete scaled real tails satisfy the free-pair criterion, that for every positive modulus and every threshold two indices beyond the threshold and congruent modulo that modulus have a non-integral difference of tails. This is an exact reformulation of the parent problem; no declaration here produces such a pair, and the problem is not decided. -/
theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail := by
  sorry
/-- For every real orbit `T` obeying the dyadic tail recurrence with integer digits `g`, the initial value `T 0` is irrational exactly when `T` satisfies the free-pair criterion. The digits are arbitrary integers and no property of the primes is used. -/
theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T := by
  sorry
/-- For every real orbit obeying the dyadic tail recurrence with integer digits, the free-pair criterion with free offset and the fixed-offset cofinal criterion are equivalent. -/
theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T := by
  sorry
/-- Every rational orbit obeying the dyadic tail recurrence with integer digits has a threshold `N₀` and a positive modulus `t` such that for all indices `N` and `M` at least `N₀` the difference `T M - T N` is an integer exactly when `N` and `M` are congruent modulo `t`. Beyond the threshold the integral pairs form one congruence lattice. -/
theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) := by
  sorry
/-- Supporting lemma identifying the modulus of that lattice: if the rational orbit obeys the dyadic tail recurrence with integer digits and the reduced denominator of `T N₀` is odd, then for indices `N` and `M` at least `N₀` the difference `T M - T N` is an integer exactly when `N` and `M` are congruent modulo the multiplicative order of 2 in the integers modulo that denominator. -/
theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by
  sorry
/-- The complete scaled real tails of the prime-gap dyadic series obey the dyadic tail recurrence whose digits are the actual consecutive prime gaps cast into the integers. The identification is unconditional and uses no rationality hypothesis. -/
theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail := by
  sorry
/-- The tail at index 0 equals `2 * S - 1`, where `S` is the sum of the prime-gap dyadic series, so `S` and that tail have the same rationality status. -/
theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by
  sorry
end PalomarCorpus.E251.FreePairEquivalence

namespace PalomarCorpus.E251.KernelDenominatorFloor
open scoped BigOperators
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
/-- Trial-division search step: `noSmallDivisor m fuel k` is true exactly when no integer `j` with `k <= j < k + fuel` and `j * j <= m` divides `m`, the recursion stopping as soon as `m < k * k`. -/
noncomputable def noSmallDivisor (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if m < k * k then true
      else if m % k == 0 then false
      else noSmallDivisor m fuel (k + 1)
/-- Kernel-evaluable trial-division primality test: true exactly when `2 <= m` and no integer at least 2 whose square is at most `m` divides `m`. -/
noncomputable def isPrimeTD (m : ℕ) : Bool := decide (2 ≤ m) && noSmallDivisor m m 2
/-- After processing every `m` below the given index, the pair whose first component counts the primes found and whose second component is the scaled prefix `sum over i below that count of prime0 i * 2 ^ (B - i - 1)`, the integer numerator of the truncated prime dyadic series at scale `2 ^ B`. -/
noncomputable def primeSumLoop (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
      let s := primeSumLoop B m
      if isPrimeTD m then (s.1 + 1, s.2 + m * 2 ^ (B - s.1 - 1)) else s
/-- The six integer conditions the Lean kernel decides for a Farey certificate: the trial-division sieve below `X` finds exactly `c` primes, `v` and `v'` are positive, the Farey determinant `u' * v = u * v' + 1` holds, and two inequalities place the normalised prime dyadic series strictly between `u / v` and `u' / v'` once the omitted tail is bounded by `5000 * (c + 1) ^ 4 / 2 ^ (c + 1)`. -/
noncomputable def certCheck (c u v u' v' X : ℕ) : Bool :=
  let s := primeSumLoop c X
  (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) &&
    decide (u * 2 ^ c < s.2 * v) &&
    decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))
/-- The sieve bound of the recorded certificate: the trial-division loop runs over every integer below 10000. -/
noncomputable def certX : ℕ := 10000
/-- The truncation index of the recorded certificate, namely 1229, the number of primes below 10000. -/
noncomputable def certC : ℕ := 1229
/-- The numerator of the lower Farey endpoint of the recorded certificate, an explicit natural number of 178 digits. -/
noncomputable def certU : ℕ :=
  8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217
/-- The denominator of the lower Farey endpoint of the recorded certificate, an explicit natural number of 178 digits; the quotient `certU / certV` agrees with the normalised prime dyadic series to more than 350 decimal places. -/
noncomputable def certV : ℕ :=
  2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745
/-- The numerator of the upper Farey endpoint of the recorded certificate, an explicit natural number of 177 digits: it satisfies `certU' * certV = certU * certV' + 1`, so `certU / certV` and `certU' / certV'` are adjacent fractions with `certU / certV` the smaller, and the certificate conditions bracket the normalised prime dyadic series strictly between them. It is a definitional literal; `cert_10000` decides those conditions on it and computes nothing from the series. -/
noncomputable def certU' : ℕ :=
  653943710149816262688241189247090522210826000856855544597530261633155217846686899097127598765624846200590981384174695232839888185316374272333277389611483117334000493867584923912
/-- The denominator of the upper Farey endpoint of the recorded certificate, an explicit natural number of 177 digits paired with `certU'` in the relation `certU' * certV = certU * certV' + 1`. The sum `certV + certV'` is the denominator bound that `den_bound_of_certCheck` returns for this certificate, and it is at least `2 ^ 589`. It is a definitional literal, not a value computed from the series. -/
noncomputable def certV' : ℕ :=
  177961107578986655119842724162170963012013632328159817663784906052492297355019687649040361529707294916566508739385806203025466313389810291243786005499164537499383612081805160767
/-- The Lean kernel re-runs the trial-division sieve over the integers below 10000 and decides that the six conditions of `certCheck` hold for the recorded certificate constants. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by
  sorry
/-- Hypotheses: the truncation index satisfies `9 <= c`, and `certCheck c u v u' v' X` is true. Conclusion: every integer `a` and positive natural `b` with the sum of the prime dyadic series equal to `a / b` satisfy `v + v' <= b`. A passing certificate turns a Farey bracket into a lower bound on the denominator of any rational representation. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by
  sorry
/-- Every representation of the normalised prime dyadic series as `a / b` with an integer `a` and a positive natural `b` has `b` at least `2 ^ 589`, a bound exceeding `10 ^ 177`. This is a finite exclusion; it is compatible with rationality of the series and proves no irrationality. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  sorry
/-- The same floor `2 ^ 589` for every representation `a / b`, with `a` an integer and `b` a positive natural number, of the consecutive-prime-gap dyadic series, whose value is 2 less than the prime series. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  sorry
end PalomarCorpus.E251.KernelDenominatorFloor

namespace PalomarCorpus.E251.LcmDiagonalCriterion
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral realTailShift tailShift)
/-- The cofinal non-integrality criterion used by this family: for every positive shift length `h` and every threshold `N₀` some index `N` at least `N₀` has `T (N + h) - T N` not an integer. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬ RealIntegral (realTailShift T h N)
/-- The schedule with value 1 at index 0 and `lcm (value at j) (j + 1)` at index `j + 1`, so that its value at `j` is the least common multiple of the integers from 1 to `j`. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
/-- For every real orbit obeying the dyadic tail recurrence with integer digits, the initial value `T 0` fails to be irrational exactly when some positive shift length `h` and some index `N` make `T (N + h) - T N` an integer. One integral positive shift anywhere is equivalent to rationality. -/
theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by
  sorry
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
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)
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
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
/-- The term of the displayed prime series with denominator `2 ^ n`: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ n`, so that the sum is `2 + 3/2 + 5/4` and so on, twice the normalised series. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
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
export PalomarCorpus.E251.Shared (prime0 primeGap0)
/-- The consecutive prime-gap sequence is not eventually periodic with any positive period. -/
theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  sorry
end PalomarCorpus.E251.PrimeGapNonperiodicity

namespace PalomarCorpus.E251.ShiftedFourPrimeCounting
open Finset
export PalomarCorpus.E251.Shared (prime0 primeGap0)
/-- The finite set of indices `n` below `N` at which the shifted gap difference `g (n + h) - g n`, computed in the integers, equals `r`. -/
noncomputable def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)
/-- The finite set of triples `(x, d, s)` with `x < prime0 N`, both `d` and `s` at most `H`, `0 < d < s`, `d + r > 0`, and all four of `x`, `x + d`, `x + s` and `x + s + d + r` prime, the last computed in the integers and cast back, which loses nothing because `0 < d + r`. These are the separated four-prime configurations produced by a shifted gap coincidence inside a window of total span at most `H`. -/
noncomputable def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z => 0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))
/-- A set of natural numbers has density zero when for every positive real `ε` all sufficiently large `N` have fewer than `ε * N` elements below `N`. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- The explicit sieve hypothesis, which this package does not prove: for every positive real `ε` there is a threshold beyond which every `N` admits a window length `H` with `(h + 1) * prime0 (N + h + 1) + (H + 1) * (number of four-prime candidates below N with window H and shift r) < ε * N * (H + 1)`. It is a named external input, not a theorem of this entry. -/
noncomputable def SeparatedQuadSieve_target (h : ℕ) (r : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ H : ℕ,
    ((h + 1 : ℕ) : ℝ) * prime0 (N + (h + 1)) +
      (H + 1 : ℕ) * ((quadCandidates N H r).card : ℝ) < ε * N * (H + 1 : ℕ)
/-- Unconditional finite counting inequality with no sieve assumption. Hypothesis: `2 <= h`. Conclusion: for every `N`, every `H` and every integer `r`, `(H + 1)` times the number of indices `n < N` with `g (n + h) - g n = r` is at most `(h + 1) * prime0 (N + h + 1)` plus `(H + 1)` times the number of separated four-prime candidates. Windows of total span at most `H` inject into those configurations, and the larger spans are bounded by the total length. -/
theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  sorry
/-- Conditional consequence. Hypotheses: `2 <= h`, and the explicit unproved separated quadruple-sieve hypothesis `SeparatedQuadSieve_target h r`. Conclusion: the set of indices `n` with `g (n + h) - g n = r` has density zero. The sieve hypothesis is not proved here, the case `h = 1` is excluded because two of the four prime positions would coincide, and density zero of these coincidences does not by itself produce the tail smallness that an irrationality proof needs. -/
theorem separated_zeroDensity_of_quad_sieve (h : ℕ) (hh : 2 ≤ h) (r : ℤ)
    (hsieve : SeparatedQuadSieve_target h r) :
    ZeroDensity {n | (primeGap0 (n + h) : ℤ) - primeGap0 n = r} := by
  sorry
end PalomarCorpus.E251.ShiftedFourPrimeCounting

namespace PalomarCorpus.E251.SparseRationalisation
export PalomarCorpus.E251.Shared (UpperBanachZero eventStarts iterlog polylog)
/-- The spacing `(k + 4) ^ 2` between consecutive support centres at schedule level `k`. -/
noncomputable def gap (k : ℕ) : ℕ := (k + 4) ^ 2
/-- The digit capacity `4 (k + 3)! 2 ^ gap k` available at schedule level `k`. -/
noncomputable def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k
/-- Level `k` is ready at index `n` for the envelope `f` when every index `m ≥ n` has `amplitude k ≤ f m` in the reals and `amplitude k ≤ m + 1` in the naturals. -/
noncomputable def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1
/-- The level used after the centre `n` when the current level is `k`: `k + 1` if level `k + 1` is ready at `n`, and `k` otherwise. -/
noncomputable def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k
/-- The schedule state (centre, level) at step `j` for the envelope `f`: `(start, 0)` at step `0`, and from the state `(c, k)` the next centre is `n = c + gap k`, with level `upgrade f n k`. -/
noncomputable def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)
/-- The `j`-th support centre of the schedule for the envelope `f` begun at `start`, the first coordinate of the schedule state; the centres increase strictly with `j`. -/
noncomputable def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1
/-- The values of `c` lying in the half-open interval `[a, a + L)`, as a finite set of natural numbers. -/
noncomputable def supportSlice (c : ℕ → ℕ) (a L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + L)).filter (fun n => n ∈ Set.range c)
/-- The proportion of starting indices `N` in `[X, 2 X)` whose length-`m` block of `a` belongs to `E`: the number of such `N` divided by `X`. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Finset.Ico X (2 * X)) m E).card / (X : ℝ)
/-- The mean over starting indices `N` in `[X, 2 X)` of the test `Φ` evaluated at `N` and at the length-`m` block of `a` starting at `N`, the sum divided by `X`. -/
noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Finset.Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X
/-- The total variation distance between the length-`m` block distributions of `a` and `b` over starting indices in `[X, 2 X)`, in the supremum-over-events convention: the supremum over all sets `E` of blocks of `|eventFrequency a X m E - eventFrequency b X m E|`. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
/-- Let `a` be any word of natural digits whose dyadic series `∑ a n / 2 ^ (n + 1)` has sum `A`, let `f` be any real envelope tending to infinity, and let `K` be any natural number. Then there are a set `S` of indices, all at least `K`, of upper Banach density zero, and reals `l < u` with `A < l`, such that every real `r` in `[l, u]` is the dyadic sum of the word `a + e` for some natural word `e` supported in `S`, eventually bounded by `f`, and such that for every positive `q` both `e n` and the prefix sum `∑ i < n, e i` are eventually divisible by `q`. The set `S` and the interval are fixed before `r` is chosen, and `[l, u]` contains rationals, so a sparse, envelope-bounded perturbation with eventual congruences at every modulus can give a rational value. The word `a` is arbitrary; nothing is asserted about the prime digits. -/
theorem arbitrary_word_sparse_rationalisation (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ Finset.range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  sorry
/-- The polylogarithmic form with block statistics. For any natural digit word `a` with dyadic sum `A`, any `ε > 0` and any natural `K`, there are a start index, reals `l < u` with `A < l`, and `C > 0` such that the centres of the schedule for the envelope `(log (n + 3)) ^ ε` begun at that index are all at least `K`, have upper Banach density zero, and number at most `C X / log (log (X + 3))` in `[X, X + L)` for all large `X` and all `L ≤ 2 X`; and every real `r` in `[l, u]` is the dyadic sum of `a + e` for a natural word `e` supported on those centres, eventually at most `(log (n + 3)) ^ ε`, with `e n` and its prefix sums eventually divisible by every positive `q`, and vanishing below `K`. For that `e` and every block length function `m` with `m X / log (log (X + 3))` tending to `0`, the total variation distance between the length-`m X` block distributions of `a` and `a + e` over `[X, 2 X)` tends to `0`, and for every `η > 0`, for all large `X`, any test `Φ` bounded by `1` in absolute value on the blocks of both words has means differing by less than `η`; the tests may depend on the starting index. The start index, the interval and `C` are fixed before `r` is chosen. -/
theorem polylogarithmic_word_interval (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ start : ℕ, ∃ l u C : ℝ,
      (Set.range (centre (polylog ε) start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre (polylog ε) start)) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice (centre (polylog ε) start) X L).card : ℝ) ≤ C * X / iterlog X) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre (polylog ε) start)) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ Finset.range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ m : ℕ → ℕ,
          Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0) →
          Tendsto (fun X => blockTV a (fun n => a n + e n) X (m X)) atTop (𝓝 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
            ∀ Φ : ℕ → (Fin (m X) → ℕ) → ℝ,
              (∀ N ∈ Finset.Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1) →
              (∀ N ∈ Finset.Ico X (2 * X), |Φ N (fun i => a (N + i.val) + e (N + i.val))| ≤ 1) →
              |testMean a X (m X) Φ - testMean (fun n => a n + e n) X (m X) Φ| < η := by
  sorry
/-- Let `a` and `b` be sequences with values in an arbitrary type that differ only at centres of the schedule for the envelope `(log (n + 3)) ^ β`, with `β > 0` and any start index. For every block length function `m` with `m X / log (log (X + 3))` tending to `0`, the total variation distance between the length-`m X` block distributions of `a` and `b` over starting indices in `[X, 2 X)` tends to `0`. The block alphabet is arbitrary and the letters are not rescaled. -/
theorem growing_block_TV {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start))
    (m : ℕ → ℕ) (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0)) :
    Tendsto (fun X => blockTV a b X (m X)) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E251.SparseRationalisation

namespace PalomarCorpus.E251.UniformSparseRationalisation
open Filter Topology
open scoped BigOperators
open Finset
export PalomarCorpus.E251.Shared (UpperBanachZero eventStarts iterlog polylog)
/-- The fraction, normalized by X, of starts in [X, 2X) whose length-m block lies in the event. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)
/-- The supremum over block events of the absolute difference of their frequencies for the two words. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
/-- The elements of S in the half-open interval [a, a + L). -/
noncomputable def supportSlice (S : Set ℕ) (a L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + L)).filter (fun n => n ∈ S)
/-- One support, target interval, counting constant and divisibility-cutoff function work for every target in the interval. The support has zero upper Banach density, satisfies the stated quantitative counting bound, and uniformly controls growing-block variation for every word changed only there; the constructed perturbations satisfy the polylogarithmic envelope, common divisibility cutoffs and exact finite-window variation bound. -/
theorem polylogarithmic_word_interval_uniform (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u C : ℝ, ∃ Nq : ℕ → ℕ,
      (S ⊆ Set.Ici K) ∧
      UpperBanachZero (S) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice S X L).card : ℝ) ≤ C * X / iterlog X) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
          ∀ b : ℕ → ℕ,
            (∀ n, a n ≠ b n → n ∈ S) →
            blockTV a b X (m X) < η) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ X m : ℕ, blockTV a (fun n => a n + e n) X m ≤
          (m : ℝ) * (supportSlice S X (X + m)).card / X := by
  sorry
/-- For every envelope tending to infinity, one support of zero upper Banach density, one target interval and one divisibility-cutoff function work for every target in that interval; the positive perturbations eventually obey the envelope and preserve the prescribed initial segment. -/
theorem arbitrary_word_sparse_rationalisation_uniform (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  sorry
end PalomarCorpus.E251.UniformSparseRationalisation
