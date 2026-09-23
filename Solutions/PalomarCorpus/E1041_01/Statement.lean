/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_01

Every non-theorem declaration of `PalomarCorpus/E1041_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped ENNReal
open Polynomial
open Metric
open Set
open scoped NNReal
open scoped ComplexConjugate
open scoped BigOperators
open Real
open MeasureTheory
open scoped UpperHalfPlane

namespace PalomarCorpus.E1041_01.Shared
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
/-- A public function spelling exactly the trinomial in both papers. Local copy of ErdosProblems.Erdos1041.PaperTrinomial.polynomialValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b
/-- The paper's `w(d,r) = arccos (clamp ((cosh d cosh r - cosh (D/2))/(sinh d sinh r)))`, the half-width of the arc cut from the hyperbolic circle of radius `r` about the centre by the open hyperbolic ball of radius `D/2` about a point at distance `d` from the centre. `clamp` truncates to `[-1,1]`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.sliceHalfAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sliceHalfAngle (D d r : ℝ) : ℝ :=
  arccos (max (-1) (min 1 ((cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r))))
end PalomarCorpus.E1041_01.Shared

namespace PalomarCorpus.E1041.PaperStatementsA
open scoped ENNReal
open Polynomial
open Metric
end PalomarCorpus.E1041.PaperStatementsA

namespace PalomarCorpus.E1041.PaperStatementsAA
open Set
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
end PalomarCorpus.E1041.PaperStatementsAA

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
export PalomarCorpus.E1041_01.Shared (polynomialValue)
end PalomarCorpus.E1041.PaperStatementsH

namespace PalomarCorpus.E1041.PaperStatementsZA
open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalMinimum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalMinimum (p : ℂ[X]) (μ : ℝ) : Prop :=
  IsLeast {x : ℝ | ∃ c : ℂ, p.derivative.eval c = 0 ∧ x = ‖p.eval c‖} μ
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.HasDistinctConnection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b
/-- Target shared by both `res:low-critical-thirteen-twentyfifths` rows. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.LowCriticalThirteenTwentyFifths, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
/-- Main bound in both scale-free corollaries. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ScaledLowCritical, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))
/-- The additional `5/2` bound in the short-note scaling corollary. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ScaledLowCriticalFiveHalves, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))
end PalomarCorpus.E1041.PaperStatementsZA

namespace PalomarCorpus.E1041.PaperStatementsAC
open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane
export PalomarCorpus.E1041_01.Shared (polar polarDen_pos sliceHalfAngle)
/-- The paper's `δ(a) = -log(1 - e^{-1/a})`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.delta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def delta (a : ℝ) : ℝ := -log (1 - exp (-(1 / a)))
/-- The paper's `λ(d) = -log tanh(d/2)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.lam, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lam (d : ℝ) : ℝ := -log (tanh (d / 2))
end PalomarCorpus.E1041.PaperStatementsAC

namespace PalomarCorpus.E1041.PaperStatementsC
open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane
export PalomarCorpus.E1041_01.Shared (polar polarDen_pos)
end PalomarCorpus.E1041.PaperStatementsC

namespace PalomarCorpus.E1041.PaperStatementsZ
open Real
open Set
open MeasureTheory
export PalomarCorpus.E1041_01.Shared (sliceHalfAngle)
end PalomarCorpus.E1041.PaperStatementsZ
