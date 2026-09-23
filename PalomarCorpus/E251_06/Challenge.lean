/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, the actual prime gap tail, affine circularity and all residue logarithmic countermodel families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace PalomarCorpus.E251_06.Shared
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
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
/-- The term of the consecutive-prime-gap dyadic series: the `n`th prime gap, cast to a real number, divided by `2 ^ (n + 1)`. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251_06.Shared

namespace PalomarCorpus.E251.ActualPrimeGapTail
open scoped BigOperators
export PalomarCorpus.E251_06.Shared (DyadicTailRecurrence RatIntegral prime0 primeGap0 primeGapDyadicTerm tailShift)
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
export PalomarCorpus.E251_06.Shared (DyadicTailRecurrence RatIntegral tailShift)
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

namespace PalomarCorpus.E251.FreePairEquivalence
open scoped BigOperators
export PalomarCorpus.E251_06.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral prime0 primeGap0 primeGapDyadicTerm realTailShift)
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
export PalomarCorpus.E251_06.Shared (prime0 primeGap0 primeGapDyadicTerm)
/-- The term of the normalised prime dyadic series: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ (n + 1)`. The sum over `n` at least 0 is `2/2 + 3/4 + 5/8` and so on, the value whose irrationality Erdős problem 251 asks about. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
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
export PalomarCorpus.E251_06.Shared (RealDyadicTailRecurrence RealIntegral realTailShift)
/-- For every real orbit obeying the dyadic tail recurrence with integer digits, the initial value `T 0` fails to be irrational exactly when some positive shift length `h` and some index `N` make `T (N + h) - T N` an integer. One integral positive shift anywhere is equivalent to rationality. -/
theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by
  sorry
end PalomarCorpus.E251.LcmDiagonalCriterion
