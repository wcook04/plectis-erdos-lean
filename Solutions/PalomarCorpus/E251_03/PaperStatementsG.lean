/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail
import Solutions.PalomarCorpus.E251_03.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsG

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)

noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)

noncomputable def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))

theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := @ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity

theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) := @ErdosProblems.Erdos251.PaperR7.irrationality_reformulation

theorem polynomial_countermodel :
    (∀ n, 0 < polynomialGapWord n) ∧
    (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
    StrictMono polynomialGapWord ∧
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
    (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = 4 * (n : ℤ) + 10) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
      polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
    HasSum (fun n : ℕ => (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)) 32 := @ErdosProblems.Erdos251.PaperR7.polynomial_countermodel

theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N := @ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic h hh

theorem rational_bounded_perturbation {a : ℕ → ℕ}
    (ha : Summable (fun n => (a n : ℝ) / 2 ^ (n + 1)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (δ : ℕ → ℕ) (r : ℚ),
      (∀ n, δ n = 0 ∨ δ n = 1) ∧
      (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((a n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) := @ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation a ha M K hM

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
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)) := @ErdosProblems.Erdos251.PaperR7.rational_small_pair_bundle g T hrec h

theorem rationality_classification {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    (¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N)) ∧
    (¬ Irrational (T 0) ↔
      ∃ h N₀ : ℕ, 0 < h ∧
        ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N, ¬ RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔ CofinalNonintegralTailShifts T) := @ErdosProblems.Erdos251.PaperR7.rationality_classification g T hrec

theorem real_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < realTailShift T h N ∧ realTailShift T h N < 1 ∧
      -1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1 ∧
      g (N + h + 1) ≠ g (N + 1)) ↔
    ((g (N + h + 1) - g (N + 1) = 2 ∧
       1 / 2 < realTailShift T h N ∧ realTailShift T h N < 1) ∨
     (g (N + h + 1) - g (N + 1) = -2 ∧
       -1 < realTailShift T h N ∧ realTailShift T h N < -(1 / 2))) := @ErdosProblems.Erdos251.PaperR7.real_signed_two_window g T hrec h N heven

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
      Irrational (∑' n : ℕ, primeDyadicTerm n)) := @ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint g T hrec h

theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n := @ErdosProblems.Erdos251.carryPartialSum_eq K n

theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1) := @ErdosProblems.Erdos251.dyadicPartialSumQ_eq_start_add_differences P n

theorem irrational_realPrimeGapTail_zero_iff :
    Irrational (realPrimeGapTail 0) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := @ErdosProblems.Erdos251.irrational_realPrimeGapTail_zero_iff

theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := @ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap hprime

theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1) := @ErdosProblems.Erdos251.prime0_dyadic_summation_by_parts n

theorem realPrimeGapTail_eq_tsum_shifted_gaps (N : ℕ) :
    realPrimeGapTail N =
      ∑' k : ℕ, (primeGap0 (N + k + 1) : ℝ) / 2 ^ (k + 1) := @ErdosProblems.Erdos251.realPrimeGapTail_eq_tsum_shifted_gaps N

theorem realPrimeGapTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail := @ErdosProblems.Erdos251.realPrimeGapTail_recurrence

theorem realPrimeGapTail_zero :
    realPrimeGapTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := @ErdosProblems.Erdos251.realPrimeGapTail_zero

theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N) := @ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den g T hrec N hodd

end PalomarCorpus.E251.PaperStatementsG
