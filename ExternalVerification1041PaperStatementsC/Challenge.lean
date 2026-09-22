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
`ErdosProblems.Erdos1041.PaperCompleteR21.HyperbolicLawOfCosines`.
-/

open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane

namespace Erdos249257.ExternalVerification1041PaperStatementsC

noncomputable def polarDen_pos (d θ : ℝ) : 0 < cosh d - sinh d * cos θ := by
  have hsq := Real.cosh_sq_sub_sinh_sq d
  have hpos := Real.cosh_pos d
  have habs : |sinh d| < cosh d := by
    nlinarith [sq_abs (sinh d), abs_nonneg (sinh d)]
  have h2 : sinh d * cos θ ≤ |sinh d| := by
    calc sinh d * cos θ ≤ |sinh d * cos θ| := le_abs_self _
      _ = |sinh d| * |cos θ| := abs_mul _ _
      _ ≤ |sinh d| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg _)
      _ = |sinh d| := mul_one _
  linarith

noncomputable def polar (d θ : ℝ) : ℍ :=
  ⟨⟨-(sinh d * sin θ) / (cosh d - sinh d * cos θ), 1 / (cosh d - sinh d * cos θ)⟩,
    one_div_pos.mpr (polarDen_pos d θ)⟩

/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂) := by
  sorry

/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dist_polar_I in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d| := by
  sorry

/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.exists_polar in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z := by
  sorry

/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar_zero_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsC
