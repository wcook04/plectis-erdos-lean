/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #68

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos68.ChannelIntegralCongruence`,
`ErdosProblems.Erdos68.PaperCompleteExisting`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification68PaperStructuresD

noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)

noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail

/-- States long68:res:product-lcm from the long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  sorry

end Erdos249257.ExternalVerification68PaperStructuresD
