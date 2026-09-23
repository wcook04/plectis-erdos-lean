/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.DynamicCancellation

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.DynamicCancellation`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification243PaperStatementsH

theorem cancellationFree_curvature_square
    {a aNext p pNext pNextNext q : ℤ}
    (hq : q = a * p - pNext)
    (hrec : pNextNext + a ^ 2 * p = (a + aNext) * pNext) :
    q ^ 2 + (p * pNextNext - pNext ^ 2) =
      (aNext - a) * p * pNext := @ErdosProblems.Erdos243.cancellationFree_curvature_square a aNext p pNext pNextNext q hq hrec

end Erdos249257.ExternalVerification243PaperStatementsH
