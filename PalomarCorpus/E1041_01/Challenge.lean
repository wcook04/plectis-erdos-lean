/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, record sections 1 to 3: the historical question; trinomials; a small least critical value

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
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
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_ani_degree_seven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_ani_degree_seven :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
          γ 0 = z₁ → γ 1 = z₂ →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) →
          (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsA

namespace PalomarCorpus.E1041.PaperStatementsAA
open Set
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
/-- States res:trinomial-all-degree from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complete_trinomial {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z₁ z₂ : ℂ} (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    Continuous (hub z₁ 0 z₂) ∧
    hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
    (∀ t ∈ Icc (0 : ℝ) 2,
      ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
    BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal = ‖z₁‖ + ‖z₂‖ ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  sorry
/-- States res:trinomial-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_degree_monic_trinomials_whole
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1) :
    (∀ z : ℂ, polynomialValue n m a b z = 0 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1) ∧
    ∀ z₁ z₂ : ℂ,
      polynomialValue n m a b z₁ = 0 →
      polynomialValue n m a b z₂ = 0 → z₁ ≠ z₂ →
      Continuous (hub z₁ 0 z₂) ∧
      hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
      (∀ t ∈ Icc (0 : ℝ) 2,
        ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
      BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal =
        ‖z₁‖ + ‖z₂‖ ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAA

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- States res:trinomial-all-degree from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomial.all_spokes in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1 := by
  sorry
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
/-- States res:scaled-low-critical, res:scaled-low-critical-path from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves := by
  sorry
/-- States res:low-critical-scale-free, res:scaled-low-critical from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical := by
  sorry
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

namespace PalomarCorpus.E1041.PaperStatementsC
open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane
export PalomarCorpus.E1041_01.Shared (polar polarDen_pos)
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

namespace PalomarCorpus.E1041.PaperStatementsZ
open Real
open Set
open MeasureTheory
export PalomarCorpus.E1041_01.Shared (sliceHalfAngle)
/-- States res:circle-slice-packing from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.circle_slice_packing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem circle_slice_packing {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π := by
  sorry
end PalomarCorpus.E1041.PaperStatementsZ
