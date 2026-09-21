/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band g

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- Cofinal failure of integral shifts for every fixed positive length. Local copy of ErdosProblems.Erdos251.CofinalNonintegralTailShifts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- The coefficient emitted by an unrestricted integer carry. Local copy of ErdosProblems.Erdos251.carryCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)
/-- The finite dyadic series emitted by `carryCoeff`. Local copy of ErdosProblems.Erdos251.carryPartialSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)
/-- Finite dyadic partial sum of the forward differences of a sequence. Local copy of ErdosProblems.Erdos251.dyadicDifferencePartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)
/-- Finite zero-based dyadic partial sum of a rational sequence. Local copy of ErdosProblems.Erdos251.dyadicPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)
/-- A positive even polynomial gap word. It is not the actual prime-gap word; it is an exact stress test for attempts using only coarse gap properties. Local copy of ErdosProblems.Erdos251.polynomialGapWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)
/-- The rational polynomial tail orbit paired with `polynomialGapWord`. Local copy of ErdosProblems.Erdos251.polynomialTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The term with denominator `2^n` used by the displayed formal conjecture. Local copy of ErdosProblems.Erdos251.primeDisplayedDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
/-- The real term in the normalized zero-based prime series. Local copy of ErdosProblems.Erdos251.primeDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- The real term in the corresponding consecutive-prime-gap series. Local copy of ErdosProblems.Erdos251.primeGapDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- Finite dyadic partial sum of the actual consecutive prime gaps. Local copy of ErdosProblems.Erdos251.primeGapPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- The genuine scaled tail after the first `N+1` prime-gap terms. Local copy of ErdosProblems.Erdos251.realPrimeGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
/-- States long251:res:infinite, res:infinite, res:irr-equivalence from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry
/-- States long251:res:irr-equivalence, res:irr-equivalence from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.irrationality_reformulation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) := by
  sorry
/-- States long251:res:polynomialcountermodel from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.polynomial_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem polynomial_countermodel :
    (∀ n, 0 < polynomialGapWord n) ∧
    (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
    StrictMono polynomialGapWord ∧
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
    (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = 4 * (n : ℤ) + 10) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
      polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
    HasSum (fun n : ℕ => (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)) 32 := by
  sorry
/-- States long251:res:gap-nonperiodic, res:gap-nonperiodic from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N := by
  sorry
/-- States long251:res:boundedperturbation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_bounded_perturbation {a : ℕ → ℕ}
    (ha : Summable (fun n => (a n : ℝ) / 2 ^ (n + 1)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (δ : ℕ → ℕ) (r : ℚ),
      (∀ n, δ n = 0 ∨ δ n = 1) ∧
      (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((a n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) := by
  sorry
/-- States long251:res:smallpair from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rational_small_pair_bundle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_small_pair_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RatIntegral (tailShift T h N) ∧ RatIntegral (tailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)) := by
  sorry
/-- States long251:res:escape-irrational, res:escape-irrational from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rationality_classification in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rationality_classification {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    (¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N)) ∧
    (¬ Irrational (T 0) ↔
      ∃ h N₀ : ℕ, 0 < h ∧
        ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N, ¬ RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔ CofinalNonintegralTailShifts T) := by
  sorry
/-- States long251:res:signedwindow from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_signed_two_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < realTailShift T h N ∧ realTailShift T h N < 1 ∧
      -1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1 ∧
      g (N + h + 1) ≠ g (N + 1)) ↔
    ((g (N + h + 1) - g (N + 1) = 2 ∧
       1 / 2 < realTailShift T h N ∧ realTailShift T h N < 1) ∨
     (g (N + h + 1) - g (N + 1) = -2 ∧
       -1 < realTailShift T h N ∧ realTailShift T h N < -(1 / 2))) := by
  sorry
/-- States long251:res:smallpair-real from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_small_pair_prime_endpoint {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RealIntegral (realTailShift T h N) ∧ RealIntegral (realTailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    ((∀ h' : ℕ, 0 < h' → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((-1 < realTailShift realPrimeGapTail h' N ∧
        realTailShift realPrimeGapTail h' N < 1) ∧
       (-1 < realTailShift realPrimeGapTail h' (N + 1) ∧
        realTailShift realPrimeGapTail h' (N + 1) < 1)) ∧
      primeGap0 (N + h' + 1) ≠ primeGap0 (N + 1)) →
      Irrational (∑' n : ℕ, primeDyadicTerm n)) := by
  sorry
/-- States long251:res:telescope from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.carryPartialSum_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n := by
  sorry
/-- States long251:res:abel from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.dyadicPartialSumQ_eq_start_add_differences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1) := by
  sorry
/-- States res:infinite from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.irrational_realPrimeGapTail_zero_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_realPrimeGapTail_zero_iff :
    Irrational (realPrimeGapTail 0) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry
/-- States res:infinite from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry
/-- States long251:res:parts from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.prime0_dyadic_summation_by_parts in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1) := by
  sorry
/-- States res:infinite from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.realPrimeGapTail_eq_tsum_shifted_gaps in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrimeGapTail_eq_tsum_shifted_gaps (N : ℕ) :
    realPrimeGapTail N =
      ∑' k : ℕ, (primeGap0 (N + k + 1) : ℝ) / 2 ^ (k + 1) := by
  sorry
/-- States res:infinite from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.realPrimeGapTail_recurrence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrimeGapTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail := by
  sorry
/-- States res:infinite from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.realPrimeGapTail_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrimeGapTail_zero :
    realPrimeGapTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by
  sorry
/-- States long251:xr:totient from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N) := by
  sorry
end PalomarCorpus.E251.PaperStatementsG
