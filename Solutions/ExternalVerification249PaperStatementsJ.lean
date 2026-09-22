/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.SignedQMomentObstruction
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.SignedQMomentObstruction`,
`ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits`.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsJ

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

theorem b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half :
    mobiusMersenneTheta 2 = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := @ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half

end Erdos249257.ExternalVerification249PaperStatementsJ
