/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperWeightedRefinementsR10`.
-/

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex

namespace Erdos249257.ExternalVerification1041PaperStatementsL

/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsL
