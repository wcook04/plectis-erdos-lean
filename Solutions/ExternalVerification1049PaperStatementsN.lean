/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.HermitePadeNoGo
import ErdosProblems.Erdos1049.PaperFiniteAssembliesR7
import ErdosProblems.Erdos1049.RationalPadeArithmetic

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.HermitePadeNoGo`,
`ErdosProblems.Erdos1049.PaperFiniteAssembliesR7`,
`ErdosProblems.Erdos1049.RationalPadeArithmetic`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStatementsN

noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

noncomputable def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n

noncomputable def rationalPadeError (S : ℝ) (U V : ℤ) : ℝ :=
  (U : ℝ) * S - (V : ℝ)

noncomputable def rationalPadeExteriorDet (Un Vn Um Vm : ℤ) : ℤ :=
  Un * Vm - Um * Vn

noncomputable def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)

noncomputable def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m

theorem height_and_hankel_deficits (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) ∧
      (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma ∧
      (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := @ErdosProblems.Erdos1049.PaperR7.height_and_hankel_deficits rho sigma hrho hsigma

theorem integer_scalar_content (S : ℝ) (cn cm Un Vn Um Vm : ℤ) :
    rationalPadeError S (cn * Un) (cn * Vn) =
      (cn : ℝ) * rationalPadeError S Un Vn ∧
    rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) =
      cn * cm * rationalPadeExteriorDet Un Vn Um Vm ∧
    |rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)| =
      |cn| * |cm| * |rationalPadeExteriorDet Un Vn Um Vm| ∧
    cn * cm ∣ rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) := @ErdosProblems.Erdos1049.PaperR7.integer_scalar_content S cn cm Un Vn Um Vm

theorem pade_summand_bound_and_gap (n k m : ℤ) :
    (0 ≤ k → k ≤ n →
      rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n) ∧
    rationalPadeDenExpTwice n - rationalPadePSummandDenExpTwice n k =
      (n - k) * (3 * n - k - 1) ∧
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) ∧
    (0 ≤ n → 1 ≤ m →
      rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n) := @ErdosProblems.Erdos1049.PaperR7.pade_summand_bound_and_gap n k m

end Erdos249257.ExternalVerification1049PaperStatementsN
