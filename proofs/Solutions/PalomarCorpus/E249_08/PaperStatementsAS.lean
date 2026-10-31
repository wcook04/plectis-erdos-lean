/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.PrimePowerJumpDynamics
import Erdos249257.RepunitMobiusNumerator
import Solutions.PalomarCorpus.E249_08.Statement

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open scoped Pointwise
open scoped Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAS
export PalomarCorpus.E249_08.Shared (mobiusNumeratorPolynomial spacedRepunit)

theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := @Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_new_fibre r p m hp hpr hm

theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r := @Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_old_fibre r p m hr hp hpr hm

end PalomarCorpus.E249.PaperStatementsAS
