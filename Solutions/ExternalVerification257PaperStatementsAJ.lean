/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.MersenneLambertLadder

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.MersenneLambertLadder`.
-/

open ArithmeticFunction

namespace Erdos249257.ExternalVerification257PaperStatementsAJ

theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2 := @MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half

end Erdos249257.ExternalVerification257PaperStatementsAJ
