/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251

Every non-theorem declaration of `PalomarCorpus/E251/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E251.AffineCircularity

namespace PalomarCorpus.E251.AllResidueLogarithmicCountermodel
open Filter
open scoped BigOperators Topology
end PalomarCorpus.E251.AllResidueLogarithmicCountermodel

namespace PalomarCorpus.E251.ExactDenominatorFloors
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
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
end PalomarCorpus.E251.PolynomialShiftCountermodel

namespace PalomarCorpus.E251.PrimeGapIdentity
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
/-- The term of the displayed prime series with denominator `2 ^ n`: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ n`, so that the sum is `2 + 3/2 + 5/4` and so on, twice the normalised series. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
end PalomarCorpus.E251.PrimeGapIdentity

namespace PalomarCorpus.E251.PrimeGapNonperiodicity
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251.Shared (prime0 primeGap0)
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
end PalomarCorpus.E251.UniformSparseRationalisation
