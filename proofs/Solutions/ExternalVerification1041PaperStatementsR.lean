/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.AbelControlPolygon
import ErdosProblems.Erdos1041.PaperCompleteR20.SexticSpokeWhole

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.AbelControlPolygon`,
`ErdosProblems.Erdos1041.PaperCompleteR20.SexticSpokeWhole`.
-/

open Polynomial
open Finset

namespace Erdos249257.ExternalVerification1041PaperStatementsR

noncomputable def sextic (r z : ℂ) : ℂ :=
  z ^ 6 + (1 / 5) * r ^ 2 * z ^ 4 - (1 / 5) * r ^ 4 * z ^ 2 - r ^ 6

theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖ := @ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole

end Erdos249257.ExternalVerification1041PaperStatementsR
