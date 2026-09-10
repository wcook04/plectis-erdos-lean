/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
/-! Palomar challenge for Erdős problem #251. Parent problem remains open. See `PalomarCorpus/README.md`. -/
namespace PalomarCorpus.E251.Shared
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1)
def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = z /-- Hypothetical non-irrationality produces one rational candidate whose algebraic states are every scaled real tail of the actual gap series. -/
def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1)
def RealIntegral (x : ℝ) : Prop := ∃ z : ℤ, x = z /-- The fixed-offset cofinal criterion: every positive shift length misses integrality at arbitrarily late basepoints. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1) /-- The real term in the corresponding consecutive-prime-gap series. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)
def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ := T (N + h) - T N
def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N
end PalomarCorpus.E251.Shared
namespace PalomarCorpus.E251.ActualPrimeGapTail
open scoped BigOperators
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral prime0 primeGap0 primeGapDyadicTerm tailShift)
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ := 2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))
theorem exists_rationalPrimeGapTailState_representation_of_not_irrational (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) : ∃ S : ℚ, (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧ ∀ N, ((rationalPrimeGapTailState S N : ℚ) : ℝ) = 2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by sorry
theorem rationalPrimeGapTailState_recurrence (S : ℚ) : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) (rationalPrimeGapTailState S) := by sorry
theorem rationalPrimeGapTailShift_eventuallyIntegral (S : ℚ) : ∃ h, 0 < h ∧ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift (rationalPrimeGapTailState S) h N) := by sorry
theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small (S : ℚ) : ∃ h, 0 < h ∧ ¬ ∃ N₀, ∀ N, N₀ ≤ N → -1 < tailShift (rationalPrimeGapTailState S) h N ∧ tailShift (rationalPrimeGapTailState S) h N < 1 := by sorry
end PalomarCorpus.E251.ActualPrimeGapTail
namespace PalomarCorpus.E251.AffineCircularity
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)
def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ | 0 => 0 | r + 1 => 2 * dyadicTailBlock g N r + g (N + r + 1)
def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop := ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)
def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n
def DyadicScaleDominates (bound : ℕ → ℚ) : Prop := ∀ N q : ℕ, 0 < q → ∃ r : ℕ, 2 * bound (N + r) * q < 2 ^ r /-- The two adjacent unit windows and an even nonzero difference digit are exactly one of the two signed `±2` half-window configurations. -/
theorem adjacent_small_mismatch_iff_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h N : ℕ) (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) : (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧ -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧ g (N + h + 1) ≠ g (N + 1)) ↔ ((g (N + h + 1) - g (N + 1) = 2 ∧ 1 / 2 < tailShift T h N ∧ tailShift T h N < 1) ∨ (g (N + h + 1) - g (N + 1) = -2 ∧ -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) := by sorry
theorem cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ) (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) : (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ¬ RatAffinePowTwo (tailShift T h (N + r)) (dyadicTailBlock (shiftDigit g h) N r) r) ↔ ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by sorry
theorem cofinal_blockResidue_escape_iff_not_eventuallyIntegral {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ) (bound : ℕ → ℚ) (hbound : ∀ N, |tailShift T h N| ≤ bound N) (hscale : DyadicScaleDominates bound) : (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ∀ z : ℤ, bound (N + r) < |((dyadicTailBlock (shiftDigit g h) N r : ℤ) : ℚ) - 2 ^ r * (z : ℚ)|) ↔ ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by sorry
end PalomarCorpus.E251.AffineCircularity
namespace PalomarCorpus.E251.FreePairEquivalence
open scoped BigOperators
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral prime0 primeGap0 primeGapDyadicTerm realTailShift)
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop := ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧ ¬RealIntegral (realTailShift T h N) /-- The free-pair criterion: for every positive modulus and every cutoff, some pair of indices beyond the cutoff, congruent modulo the modulus, has a nonintegral tail difference. -/
def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop := ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧ ¬ RealIntegral (T M - T N) /-- The real scaled tail of the actual prime-gap series after the first `N+1` gaps. -/
noncomputable def primeGapRealTail (N : ℕ) : ℝ := 2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) /-- **Erdős #251 in free-pair form.**  The consecutive-prime-gap dyadic series is irrational exactly when, for every positive modulus `t` and every cutoff, two tail indices beyond the cutoff and congruent modulo `t` have a nonintegral scaled-tail difference.  Nothing here produces such pairs. -/
theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral : Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔ CofinalFreePairNonintegral primeGapRealTail := by sorry
theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : Irrational (T 0) ↔ CofinalFreePairNonintegral T := by sorry
theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T := by sorry
theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) : ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M → (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) := by sorry
theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den) {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) : RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by sorry
theorem primeGapRealTail_recurrence : RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail := by sorry
theorem primeGapRealTail_zero : primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by sorry
end PalomarCorpus.E251.FreePairEquivalence
namespace PalomarCorpus.E251.KernelDenominatorFloor
open scoped BigOperators
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
def noSmallDivisor (m : ℕ) : ℕ → ℕ → Bool | 0, _ => true | fuel + 1, k => if m < k * k then true else if m % k == 0 then false else noSmallDivisor m fuel (k + 1) /-- Trial-division primality test, kernel-evaluable. -/
def isPrimeTD (m : ℕ) : Bool := decide (2 ≤ m) && noSmallDivisor m m 2 /-- After processing all `m < X`: `(π(X), Σ_{i < π(X)} p_i 2^{B-i-1})`. -/
def primeSumLoop (B : ℕ) : ℕ → ℕ × ℕ | 0 => (0, 0) | m + 1 => let s := primeSumLoop B m if isPrimeTD m then (s.1 + 1, s.2 + m * 2 ^ (B - s.1 - 1)) else s /-- The six integer conditions the kernel decides. -/
def certCheck (c u v u' v' X : ℕ) : Bool := let s := primeSumLoop c X (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) && decide (u * 2 ^ c < s.2 * v) && decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))
def certX : ℕ := 10000
def certC : ℕ := 1229
def certU : ℕ := 8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217
def certV : ℕ := 2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by sorry
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c) (h : certCheck c u v u' v' X = true) : ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by sorry
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b) (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by sorry
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b) (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by sorry
end PalomarCorpus.E251.KernelDenominatorFloor
namespace PalomarCorpus.E251.LcmDiagonalCriterion
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral realTailShift tailShift)
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop := ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧ ¬ RealIntegral (realTailShift T h N)
def lcmDiagonalSchedule : ℕ → ℕ | 0 => 1 | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1) /-- An integer-digit real dyadic orbit starts rationally exactly when one positive tail difference is integral. -/
theorem notIrrationalInitial_iff_exists_integral_positive_tailShift {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : ¬ Irrational (T 0) ↔ ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by sorry
theorem irrationalInitial_iff_cofinalNonintegralTailShifts {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : Irrational (T 0) ↔ CofinalNonintegralTailShifts T := by sorry
theorem tailShiftIntegral_iff_orderOf_dvd {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (N h : ℕ) : RatIntegral (tailShift T h N) ↔ orderOf (2 : ZMod (T N).den) ∣ h := by sorry
theorem irrationalInitial_iff_nonintegral_on_schedule {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ) (hpos : ∀ j, 0 < s j) (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j) (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) : Irrational (T 0) ↔ ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) := by sorry
theorem irrationalInitial_iff_allLcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : Irrational (T 0) ↔ ∀ j : ℕ, ¬ RealIntegral (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by sorry
end PalomarCorpus.E251.LcmDiagonalCriterion
namespace PalomarCorpus.E251.PolynomialShiftCountermodel
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)
def polynomialTailOrbit (n : ℕ) : ℚ := (2 * (n + 4) ^ 2 : ℕ) /-- The positive-even quadratic word paired with `polynomialTailOrbit`. -/
def polynomialGapWord (n : ℕ) : ℤ := (2 * (n ^ 2 + 4 * n + 2) : ℕ) /-- The real dyadic term of the countermodel series, indexed so that `n = 0` carries the digit `g 1 / 2`.  The zero-index digit is the initial carry and is not part of the series. -/
noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ := (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1) /-- A positive, even, strictly growing polynomial digit word satisfies the dyadic recurrence while every fixed tail shift remains integral and every adjacent digit difference equals `4n + 10`, and its dyadic series sums to the rational number `32`. -/
theorem polynomialGapTailCountermodel : DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧ (∀ n, 0 < polynomialGapWord n) ∧ (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧ StrictMono polynomialGapWord ∧ (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧ (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ)) ∧ (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧ polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧ (∑' n : ℕ, polynomialGapDyadicTerm n) = 32 ∧ ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by sorry
end PalomarCorpus.E251.PolynomialShiftCountermodel
namespace PalomarCorpus.E251.PrimeGapIdentity
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ n /-- The term of the corresponding consecutive-prime-gap series. -/
theorem prime0_le_polynomial (n : ℕ) : prime0 n ≤ 1250 * (n + 1) ^ 4 := by sorry
theorem primeSeries_summable : Summable primeDyadicTerm := by sorry
theorem primeGapSeries_summable : Summable primeGapDyadicTerm := by sorry
theorem primeSeries_eq_two_add_primeGapSeries : (∑' n : ℕ, primeDyadicTerm n) = 2 + ∑' n : ℕ, primeGapDyadicTerm n := by sorry
theorem primeSeries_irrational_iff_primeGapSeries : Irrational (∑' n : ℕ, primeDyadicTerm n) ↔ Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by sorry
theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries : (∑' n : ℕ, primeDisplayedDyadicTerm n) = 4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by sorry
theorem primeDisplayedSeries_irrational_iff_primeGapSeries : Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔ Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by sorry
end PalomarCorpus.E251.PrimeGapIdentity
