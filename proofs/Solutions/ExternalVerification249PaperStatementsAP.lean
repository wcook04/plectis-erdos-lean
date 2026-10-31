/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.MersenneLambertLadder

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.MersenneLambertLadder`.
-/

open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsAP

theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ) := @MersenneLambertLadder.tsum_moebius_lambert_sq r hr0 hr1

end Erdos249257.ExternalVerification249PaperStatementsAP
