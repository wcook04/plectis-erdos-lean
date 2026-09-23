/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CyclotomicProjectionOfShadow
import Erdos249257.RadicalMobiusShadow
import Erdos249257.RepunitMobiusNumerator
import ErdosProblems.Erdos249.PaperCompleteR20.NumeratorEvaluation
import ErdosProblems.Erdos249.PaperCompleteR20.RadicalDecomposition
import ErdosProblems.Erdos249.PaperCompleteR21.DivisorChannelSplitAndSeamDoubling
import ErdosProblems.Erdos249.PaperCompleteR21.NumeratorPolynomialAndMersenneRemainder
import Solutions.PalomarCorpus.E249_07.Statement

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAQ
export PalomarCorpus.E249_07.Shared (mobiusNumeratorPolynomial spacedRepunit)

noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2

noncomputable def cyclotomicValue (m : ℕ) : ℕ :=
  (cyclotomicEval m).natAbs

noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)

noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient

noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)

theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (baseMobiusShadow r).den := @Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue_dvd_baseMobiusShadow_den r hr

theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1 := @Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_gcd_cyclotomicValue r hr

theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := @Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_mod_cyclotomicEval r m hr hm

theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      mobiusNumerator r := @Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two r hr

theorem numerator_eval_two_divisors {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      ∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((mersenne r /
            mersenne d : ℕ) : ℤ)) := @ErdosProblems.Erdos249.PaperCompleteR20.numerator_eval_two_divisors r hr

theorem radical_decomposition (H r : ℕ) (hH : 0 < H) (hr : 0 < r) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) * baseMobiusShadow (squarefreeKernel H) ∧
    (baseMobiusShadow r).den = mersenne r /
      ((mobiusNumeratorPolynomial r).eval 2).natAbs.gcd (mersenne r) := @ErdosProblems.Erdos249.PaperCompleteR20.radical_decomposition H r hH hr

theorem paperNumeratorPolynomial_eq (r : ℕ) :
    paperNumeratorPolynomial r = mobiusNumeratorPolynomial r := @ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial_eq r

theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / squarefreeKernel H : ℕ) : ℤ) *
        (gcdWordCoeff
          (squarefreeKernel H) s : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_radical_form H s hH

end PalomarCorpus.E249.PaperStatementsAQ
