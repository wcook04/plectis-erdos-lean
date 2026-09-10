/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.AffineCylinderCollapse
import Mathlib
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.KernelDenominatorFloor
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.PolynomialGapSeriesValue

namespace PalomarCorpus.E251.Shared
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Hypothetical non-irrationality produces one rational candidate whose
algebraic states are every scaled real tail of the actual gap series. -/

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The fixed-offset cofinal criterion: every positive shift length misses
integrality at arbitrarily late basepoints. -/

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1) /-- The real term in the corresponding consecutive-prime-gap series. -/

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

end PalomarCorpus.E251.Shared
import ErdosProblems.Erdos251.PrimeGapDyadicTail

open scoped BigOperators

namespace PalomarCorpus.E251.ActualPrimeGapTail
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral prime0 primeGap0 primeGapDyadicTerm tailShift)

noncomputable abbrev primeGapPartialSumQ := ErdosProblems.Erdos251.primeGapPartialSumQ
noncomputable abbrev rationalPrimeGapTailState :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState
theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) :=
  ErdosProblems.Erdos251.exists_rationalPrimeGapTailState_representation_of_not_irrational h

theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState_recurrence S

theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral S

theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 :=
  ErdosProblems.Erdos251.rationalPrimeGapTail_has_positive_shift_not_eventually_small S

end PalomarCorpus.E251.ActualPrimeGapTail

import ErdosProblems.Erdos251.AffineCylinderCollapse

namespace PalomarCorpus.E251.AffineCircularity
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)

abbrev dyadicTailBlock := ErdosProblems.Erdos251.dyadicTailBlock
abbrev RatAffinePowTwo := ErdosProblems.Erdos251.RatAffinePowTwo
abbrev shiftDigit := ErdosProblems.Erdos251.shiftDigit
abbrev DyadicScaleDominates := ErdosProblems.Erdos251.DyadicScaleDominates

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
          -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) :=
  ErdosProblems.Erdos251.adjacent_small_mismatch_iff_signed_two_window
    hrec h N heven

theorem cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) :=
  ErdosProblems.Erdos251.cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    hrec h hdiffEven

theorem cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (bound : ℕ → ℚ)
    (hbound : ∀ N, |tailShift T h N| ≤ bound N)
    (hscale : DyadicScaleDominates bound) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
      ∀ z : ℤ, bound (N + r) <
        |((dyadicTailBlock (shiftDigit g h) N r : ℤ) : ℚ) -
          2 ^ r * (z : ℚ)|) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) :=
  ErdosProblems.Erdos251.cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    hrec h bound hbound hscale

end PalomarCorpus.E251.AffineCircularity

import Mathlib
import ErdosProblems.Erdos251.FreePairReduction

open scoped BigOperators

namespace PalomarCorpus.E251.FreePairEquivalence
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral prime0 primeGap0 primeGapDyadicTerm realTailShift)

abbrev CofinalNonintegralTailShifts := ErdosProblems.Erdos251.CofinalNonintegralTailShifts
abbrev CofinalFreePairNonintegral := ErdosProblems.Erdos251.CofinalFreePairNonintegral
noncomputable abbrev primeGapRealTail := ErdosProblems.Erdos251.primeGapRealTail

theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail :=
  ErdosProblems.Erdos251.irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalFreePairNonintegral hrec

theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts hrec

theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) :=
  ErdosProblems.Erdos251.exists_free_pair_lattice hrec

theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] :=
  ErdosProblems.Erdos251.free_pair_integral_iff_modEq hrec hodd hN hM

theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail :=
  ErdosProblems.Erdos251.primeGapRealTail_recurrence

theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 :=
  ErdosProblems.Erdos251.primeGapRealTail_zero

end PalomarCorpus.E251.FreePairEquivalence

import ErdosProblems.Erdos251.KernelDenominatorFloor

open scoped BigOperators

namespace PalomarCorpus.E251.KernelDenominatorFloor
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

abbrev noSmallDivisor := ErdosProblems.Erdos251.noSmallDivisor
abbrev isPrimeTD := ErdosProblems.Erdos251.isPrimeTD
abbrev primeSumLoop := ErdosProblems.Erdos251.primeSumLoop
abbrev certCheck := ErdosProblems.Erdos251.certCheck
abbrev certX := ErdosProblems.Erdos251.certX
abbrev certC := ErdosProblems.Erdos251.certC
abbrev certU := ErdosProblems.Erdos251.certU
abbrev certV := ErdosProblems.Erdos251.certV
abbrev certU' := ErdosProblems.Erdos251.certU'
abbrev certV' := ErdosProblems.Erdos251.certV'

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true :=
  ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b :=
  ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end PalomarCorpus.E251.KernelDenominatorFloor

import ErdosProblems.Erdos251.OrderLatticeDiagonal

namespace PalomarCorpus.E251.LcmDiagonalCriterion
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral realTailShift tailShift)

abbrev CofinalNonintegralTailShifts :=
  ErdosProblems.Erdos251.CofinalNonintegralTailShifts

abbrev lcmDiagonalSchedule := ErdosProblems.Erdos251.lcmDiagonalSchedule

theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) :=
  ErdosProblems.Erdos251.not_irrational_initial_iff_exists_integral_positive_tailShift
    hrec

theorem irrationalInitial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalNonintegralTailShifts hrec

theorem tailShiftIntegral_iff_orderOf_dvd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      orderOf (2 : ZMod (T N).den) ∣ h :=
  ErdosProblems.Erdos251.tailShift_integral_iff_orderOf_dvd hrec N h

theorem irrationalInitial_iff_nonintegral_on_schedule
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) :=
  ErdosProblems.Erdos251.irrational_initial_iff_nonintegral_on_schedule
    hrec s hpos hdvd hgrow

theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) :=
  ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral hrec

end PalomarCorpus.E251.LcmDiagonalCriterion

import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.PolynomialGapSeriesValue

namespace PalomarCorpus.E251.PolynomialShiftCountermodel
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)

def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)

def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)

noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)

/-- The Comparator vocabulary word is the source word. -/
theorem polynomialGapWord_eq_source :
    polynomialGapWord = ErdosProblems.Erdos251.polynomialGapWord := rfl

/-- The Comparator vocabulary series term is the source series term. -/
theorem polynomialGapDyadicTerm_eq_source :
    polynomialGapDyadicTerm = ErdosProblems.Erdos251.polynomialGapDyadicTerm := rfl

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [DyadicTailRecurrence, polynomialGapWord, polynomialTailOrbit,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.polynomialGapWord,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_recurrence
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_pos n
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_even n
  · simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_strictMono
  · intro h N
    simpa [tailShift, RatIntegral, polynomialTailOrbit,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_shift_integral h N
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ErdosProblems.Erdos251.polynomialGapWord_succ_sub n
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ⟨ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_two n,
      ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_neg_two n⟩
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.tsum_polynomialGapDyadicTerm_eq
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.not_irrational_tsum_polynomialGapDyadicTerm

end PalomarCorpus.E251.PolynomialShiftCountermodel

import ErdosProblems.Erdos251.PrimeGapDyadicTail

namespace PalomarCorpus.E251.PrimeGapIdentity
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

noncomputable abbrev primeDisplayedDyadicTerm :=
  ErdosProblems.Erdos251.primeDisplayedDyadicTerm
theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 :=
  ErdosProblems.Erdos251.prime0_le_polynomial n

theorem primeSeries_summable : Summable primeDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeGapSeries_summable : Summable primeGapDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeGapDyadicTerm

theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional

theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

end PalomarCorpus.E251.PrimeGapIdentity
