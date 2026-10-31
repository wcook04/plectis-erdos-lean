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
`ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDefect`,
`ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDifferenceLimits`,
`ErdosProblems.Erdos243.PaperCompleteR21.RegularRateExtraction`.
-/

open Filter
open Finset

namespace Erdos249257.ExternalVerification243PaperStatementsN

noncomputable def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))

noncomputable def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)

/-- States long243:eq:regularrate, long243:res:extraction from the long record for Erdős problem
#243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ) := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsN
