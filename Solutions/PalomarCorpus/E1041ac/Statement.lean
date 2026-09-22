/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041ac

Every non-theorem declaration of `PalomarCorpus/E1041ac/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1041.PaperStatementsAC
