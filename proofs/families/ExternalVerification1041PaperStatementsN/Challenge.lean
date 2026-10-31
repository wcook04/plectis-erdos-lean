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
`ErdosProblems.Erdos1041.NewtonFlowRaySeparation`.
-/

open Set
open Metric
open AffineSubspace
open Polynomial

namespace Erdos249257.ExternalVerification1041PaperStatementsN

noncomputable def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a

/-- States res:locus from the long record and the short record for Erdős problem #1041.
Transported from ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ) := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsN
