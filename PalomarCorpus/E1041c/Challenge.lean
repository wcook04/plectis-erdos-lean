/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band c

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane

namespace PalomarCorpus.E1041.PaperStatementsC
open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane
/-- The denominator `R = cosh d - sinh d cos θ` of the polar parametrisation is positive, because `|sinh d| < cosh d`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polarDen_pos, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- **Geodesic polar coordinates on the hyperbolic plane.** `polar d θ` is the point of the upper half-plane at hyperbolic distance `|d|` from the centre `i` with argument `θ`: the image of the Poincaré-disc point `tanh (d/2) e^{iθ}` (the paper's coordinates) under the Cayley transform `w ↦ i(1+w)/(1-w)`, which is `(-(sinh d sin θ) + i)/(cosh d - sinh d cos θ)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polar (d θ : ℝ) : ℍ :=
  ⟨⟨-(sinh d * sin θ) / (cosh d - sinh d * cos θ), 1 / (cosh d - sinh d * cos θ)⟩,
    one_div_pos.mpr (polarDen_pos d θ)⟩
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂) := by
  sorry
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dist_polar_I in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d| := by
  sorry
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.exists_polar in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z := by
  sorry
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar_zero_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I := by
  sorry
end PalomarCorpus.E1041.PaperStatementsC
