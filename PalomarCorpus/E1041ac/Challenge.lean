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

namespace PalomarCorpus.E1041.PaperStatementsAC
open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane
/-- The paper's `δ(a) = -log(1 - e^{-1/a})`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.delta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def delta (a : ℝ) : ℝ := -log (1 - exp (-(1 / a)))
/-- The paper's `λ(d) = -log tanh(d/2)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.lam, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lam (d : ℝ) : ℝ := -log (tanh (d / 2))
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
/-- The paper's `w(d,r) = arccos (clamp ((cosh d cosh r - cosh (D/2))/(sinh d sinh r)))`, the half-width of the arc cut from the hyperbolic circle of radius `r` about the centre by the open hyperbolic ball of radius `D/2` about a point at distance `d` from the centre. `clamp` truncates to `[-1,1]`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.sliceHalfAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sliceHalfAngle (D d r : ℝ) : ℝ :=
  arccos (max (-1) (min 1 ((cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r))))
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem circle_slice_packing {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π := by
  sorry
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing_abstract in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem circle_slice_packing_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π := by
  sorry
/-- States res:dual-arity-floor from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor_abstract in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dual_arity_floor_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAC
