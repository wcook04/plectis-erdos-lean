/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band f

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial

namespace PalomarCorpus.E1049.PaperStatementsF
open Polynomial
/-- Integer homogeneous evaluation of an integral polynomial at `(3,2)`, using the declared ambient width `W`. Local copy of ErdosProblems.Erdos1049.homEvalThreeTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
/-- The bottom `3`-adic endpoint jet of depth `R`. Local copy of ErdosProblems.Erdos1049.bottomJet3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
/-- Integer homogeneous evaluation at a reduced numerator--denominator pair. The existing `homEvalThreeTwo` is the specialization `(a,b) = (3,2)`. This generic form is the arithmetic object used in Proposition 3.6 of the paper. Local copy of ErdosProblems.Erdos1049.homEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEval (a b W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * a ^ i * b ^ (W - i)
/-- States res:bottomjet from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.bottomJet3_eq_zero_iff_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bottomJet3_eq_zero_iff_dvd (R W : ℕ) (P : Polynomial ℤ) :
    bottomJet3 R W P = 0 ↔ ((3 ^ R : ℕ) : ℤ) ∣ homEvalThreeTwo W P := by
  sorry
/-- States long1049:res:commonmult from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.commonMultiplier_not_two_not_three_of_endpoint_units in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem commonMultiplier_not_two_not_three_of_endpoint_units
    (c : ℤ) (W : ℕ) (U V : Polynomial ℤ)
    (hUtop : U.coeff W = 1 ∨ U.coeff W = -1)
    (hVconst : V.coeff 0 = 1 ∨ V.coeff 0 = -1)
    (hcU : c ∣ homEvalThreeTwo W U)
    (hcV : c ∣ homEvalThreeTwo W V) :
    (¬ (2 : ℤ) ∣ c) ∧ (¬ (3 : ℤ) ∣ c) := by
  sorry
/-- States long1049:res:cyclounit from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.cyclotomicHomEval_isCoprime_mul in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomicHomEval_isCoprime_mul
    {a b m : ℕ} (hm : 0 < m) (hab : a.Coprime b) :
    IsCoprime
      (homEval a b (Nat.totient m) (Polynomial.cyclotomic m ℤ))
      ((a * b : ℕ) : ℤ) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsF
