/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos249.PaperCompleteR21.NumeratorPolynomialAndMersenneRemainder

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.PaperCompleteR21.NumeratorPolynomialAndMersenneRemainder`.
-/

open scoped BigOperators
open scoped Polynomial

namespace Erdos249257.ExternalVerification249PaperStatementsAO

noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)

theorem four_thirds_tsum_eighth_pow_tail (m : ℕ) :
    (4 / 3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) =
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := @ErdosProblems.Erdos249.PaperCompleteR21.four_thirds_tsum_eighth_pow_tail m

theorem mersenneRemainderTail_le {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1)) ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := @ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainderTail_le m hm

theorem mersenneRemainder_identity_and_bound {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n) ∧
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n ≤
        (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n := @ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainder_identity_and_bound n hn

theorem mersenne_dvd_of_dvd {d r : ℕ} (hd : d ∣ r) :
    (2 ^ d - 1 : ℕ) ∣ (2 ^ r - 1 : ℕ) := @ErdosProblems.Erdos249.PaperCompleteR21.mersenne_dvd_of_dvd d r hd

theorem one_sub_half_pow_ge {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ 1 - ((1 : ℝ) / 2) ^ n := @ErdosProblems.Erdos249.PaperCompleteR21.one_sub_half_pow_ge n hn

theorem paperNumerator_coeff_eq_gcd_divisor_sum {r k : ℕ} (hr : Squarefree r)
    (hk : k < r) :
    (paperNumeratorPolynomial r).coeff k =
      ∑ d ∈ (Nat.gcd r k).divisors,
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_gcd_divisor_sum r k hr hk

theorem paperNumerator_coeff_eq_zero {r k : ℕ} (hr : Squarefree r) (hk : r ≤ k) :
    (paperNumeratorPolynomial r).coeff k = 0 := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_zero r k hr hk

theorem paperNumerator_coeff_pos {r k : ℕ} (hr : Squarefree r) (hk : k < r) :
    0 < (paperNumeratorPolynomial r).coeff k := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_pos r k hr hk

theorem paperNumerator_eq_gcdWordForm {r : ℕ} (hr : Squarefree r) :
    paperNumeratorPolynomial r =
      ∑ k ∈ Finset.range r,
        Polynomial.C (((r / Nat.gcd r k) * Nat.totient (Nat.gcd r k) : ℕ) : ℤ) *
          (Polynomial.X : Polynomial ℤ) ^ k := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eq_gcdWordForm r hr

theorem paperNumerator_eval_two {r : ℕ} (_hr : Squarefree r) :
    (((paperNumeratorPolynomial r).eval 2 : ℤ) : ℚ) =
      ∑ d ∈ r.divisors,
        (ArithmeticFunction.moebius d : ℚ) * ((r / d : ℕ) : ℚ) *
          (((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1)) := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two r _hr

theorem paperNumerator_eval_two_primeSubsetForm {r : ℕ} (hr : Squarefree r) :
    (paperNumeratorPolynomial r).eval 2 =
      ∑ s ∈ r.primeFactors.powerset,
        (-1 : ℤ) ^ s.card * ((r / s.prod id : ℕ) : ℤ) *
          ((((2 ^ r - 1) / (2 ^ s.prod id - 1) : ℕ)) : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two_primeSubsetForm r hr

theorem tsum_eighth_pow_tail (m : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := @ErdosProblems.Erdos249.PaperCompleteR21.tsum_eighth_pow_tail m

end Erdos249257.ExternalVerification249PaperStatementsAO
