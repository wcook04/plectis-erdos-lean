/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.ProductDefectThresholds`.
-/

open Filter

namespace Erdos249257.ExternalVerification243PaperStatementsF

/-- States long243:res:onethreshold from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_strict_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem original_coordinate_strict_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (r : ℝ) (hr : r < 1)
    (hlimsup : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsF
