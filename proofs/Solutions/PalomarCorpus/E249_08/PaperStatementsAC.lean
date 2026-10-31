/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CyclotomicProjectionOfShadow
import Erdos249257.RepunitMobiusNumerator
import Solutions.PalomarCorpus.E249_08.Statement

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAC
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)

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

end PalomarCorpus.E249.PaperStatementsAC
