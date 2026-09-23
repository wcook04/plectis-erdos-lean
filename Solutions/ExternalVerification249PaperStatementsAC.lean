/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CyclotomicProjectionOfShadow
import Erdos249257.RepunitMobiusNumerator

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CyclotomicProjectionOfShadow`, `Erdos249257.RepunitMobiusNumerator`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

namespace Erdos249257.ExternalVerification249PaperStatementsAC

noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)

noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient

noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1

noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)

theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := @Erdos249257.CyclotomicProjectionOfShadow.cyclotomic_dvd_mobiusNumeratorPolynomial_sub r m hr hm

theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1) := @Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo_eq_prod_primeFactors n hn

theorem mobiusNumeratorPolynomial_coeff {r k : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).coeff k =
      if k < r then (gcdWordCoeff r k : ℤ) else 0 := @Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff r k hr

theorem mobiusNumeratorPolynomial_coeff_pos {r k : ℕ}
    (hr : Squarefree r) (hk : k < r) :
    0 < (mobiusNumeratorPolynomial r).coeff k := @Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff_pos r k hr hk

end Erdos249257.ExternalVerification249PaperStatementsAC
