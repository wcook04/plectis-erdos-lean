/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band n

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
/-- Cyclotomic denominator-saving expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpCyclotomicSaving, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- Quadratic Archimedean decay expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpDecay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- Homogeneous polynomial-width expression in the rectangular exponent model. Local copy of ErdosProblems.Erdos1049.hpHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- Rational-base height threshold associated with the explicit exponent model above. Local copy of ErdosProblems.Erdos1049.hpThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
/-- Twice the proposed common denominator exponent `Eₙ = (3n² - n) / 2`. Local copy of ErdosProblems.Erdos1049.rationalPadeDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n
/-- The real error of an integer Padé coefficient pair `(U,V)` at `S`. Local copy of ErdosProblems.Erdos1049.rationalPadeError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeError (S : ℝ) (U V : ℤ) : ℝ :=
  (U : ℝ) * S - (V : ℝ)
/-- The exterior determinant of two integer Padé coefficient pairs. For the adjacent Zudilin construction this is `Uₙ Vₘ - Uₘ Vₙ`. Unlike either individual coefficient pair, the determinant can inherit every divisor common to the two `U` coefficients and every divisor common to the two `V` coefficients. Local copy of ErdosProblems.Erdos1049.rationalPadeExteriorDet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeExteriorDet (Un Vn Um Vm : ℤ) : ℤ :=
  Un * Vm - Um * Vn
/-- Twice the denominator exponent of the `k`-th summand in the homogenised little-`q` Legendre `P` polynomial. Local copy of ErdosProblems.Erdos1049.rationalPadePSummandDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)
/-- Twice the maximal denominator exponent in the `Q`-summand calculation, after the change of variables `j = n - m - 1`. Local copy of ErdosProblems.Erdos1049.rationalPadeQMaxDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m
/-- States long1049:res:sharpgaps from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.height_and_hankel_deficits in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem height_and_hankel_deficits (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) ∧
      (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma ∧
      (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  sorry
/-- States long1049:res:content, res:content from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.integer_scalar_content in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem integer_scalar_content (S : ℝ) (cn cm Un Vn Um Vm : ℤ) :
    rationalPadeError S (cn * Un) (cn * Vn) =
      (cn : ℝ) * rationalPadeError S Un Vn ∧
    rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) =
      cn * cm * rationalPadeExteriorDet Un Vn Um Vm ∧
    |rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)| =
      |cn| * |cm| * |rationalPadeExteriorDet Un Vn Um Vm| ∧
    cn * cm ∣ rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) := by
  sorry
/-- States long1049:res:pade, res:pade from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.pade_summand_bound_and_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pade_summand_bound_and_gap (n k m : ℤ) :
    (0 ≤ k → k ≤ n →
      rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n) ∧
    rationalPadeDenExpTwice n - rationalPadePSummandDenExpTwice n k =
      (n - k) * (3 * n - k - 1) ∧
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) ∧
    (0 ≤ n → 1 ≤ m →
      rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsN
