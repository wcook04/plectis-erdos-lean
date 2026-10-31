/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldCoordinates
import ErdosProblems.Erdos243.PaperCompleteR20.ScaleTwelve

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldCoordinates`,
`ErdosProblems.Erdos243.PaperCompleteR20.ScaleTwelve`.
-/

open Polynomial
open scoped BigOperators

namespace Erdos249257.ExternalVerification243PaperStatementsP

noncomputable def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η

theorem scale_twelve_of_square_in_rootField
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hsquare : ∃ β : L,
      β ∈ IntermediateField.adjoin ℚ ({α} : Set L) ∧
      β ^ 2 = α ^ 2 - 1) :
    m = 12 := @ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField L inferInstance inferInstance m c hm hc α hirr hroot hsquare

end Erdos249257.ExternalVerification243PaperStatementsP
