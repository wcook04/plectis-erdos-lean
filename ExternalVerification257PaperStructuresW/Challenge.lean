/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusGlobalRepair`,
`ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily`.
-/

open Filter
open Set
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresW

structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d

/-- States record:257bm-c3 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_bit_stable in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_compatible_bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ} (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresW
