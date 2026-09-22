/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Solutions.PalomarCorpus.E1049f.Statement

open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsF

theorem bottomJet3_eq_zero_iff_dvd (R W : ℕ) (P : Polynomial ℤ) :
    bottomJet3 R W P = 0 ↔ ((3 ^ R : ℕ) : ℤ) ∣ homEvalThreeTwo W P := @ErdosProblems.Erdos1049.bottomJet3_eq_zero_iff_dvd R W P

theorem commonMultiplier_not_two_not_three_of_endpoint_units
    (c : ℤ) (W : ℕ) (U V : Polynomial ℤ)
    (hUtop : U.coeff W = 1 ∨ U.coeff W = -1)
    (hVconst : V.coeff 0 = 1 ∨ V.coeff 0 = -1)
    (hcU : c ∣ homEvalThreeTwo W U)
    (hcV : c ∣ homEvalThreeTwo W V) :
    (¬ (2 : ℤ) ∣ c) ∧ (¬ (3 : ℤ) ∣ c) := @ErdosProblems.Erdos1049.commonMultiplier_not_two_not_three_of_endpoint_units c W U V hUtop hVconst hcU hcV

theorem cyclotomicHomEval_isCoprime_mul
    {a b m : ℕ} (hm : 0 < m) (hab : a.Coprime b) :
    IsCoprime
      (homEval a b (Nat.totient m) (Polynomial.cyclotomic m ℤ))
      ((a * b : ℕ) : ℤ) := @ErdosProblems.Erdos1049.cyclotomicHomEval_isCoprime_mul a b m hm hab

end PalomarCorpus.E1049.PaperStatementsF
