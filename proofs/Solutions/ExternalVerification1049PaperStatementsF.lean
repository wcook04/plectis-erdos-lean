/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.ZudilinConeArithmetic

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.ZudilinConeArithmetic`.
-/

open Polynomial

namespace Erdos249257.ExternalVerification1049PaperStatementsF

noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)

noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P

noncomputable def homEval (a b W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * a ^ i * b ^ (W - i)

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

end Erdos249257.ExternalVerification1049PaperStatementsF
