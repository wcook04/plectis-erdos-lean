/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, note sections 1 to 7: monic trinomials, in every degree; critical proximity and straight-path obstructions; solved polynomial families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Polynomial
open Finset
open scoped BigOperators
open Set
open scoped NNReal
open scoped ENNReal
open scoped ComplexConjugate
open Metric
open AffineSubspace

namespace PalomarCorpus.E1041_05.Shared
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- `p(z) = z^8 - (3/2)z`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobePolynomial : ℂ[X] := X ^ 8 - C (3 / 2) * X
/-- The closed unit sublevel set of `p`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobeSublevel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobeSublevel : Set ℂ := {z : ℂ | ‖lobePolynomial.eval z‖ ≤ 1}
/-- `C`: the connected component of `{|p| ≤ 1}` containing the origin. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobeComponent, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobeComponent : Set ℂ := connectedComponentIn lobeSublevel 0
end PalomarCorpus.E1041_05.Shared

namespace PalomarCorpus.E1041.PaperStatementsR
open Polynomial
open Finset
/-- The stored sextic guardrail family `f_r z = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6`. Local copy of ErdosProblems.Erdos1041.AbelControlPolygon.sextic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sextic (r z : ℂ) : ℂ :=
  z ^ 6 + (1 / 5) * r ^ 2 * z ^ 4 - (1 / 5) * r ^ 4 * z ^ 2 - r ^ 6
/-- States res:sextic-spoke from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖ := by
  sorry
end PalomarCorpus.E1041.PaperStatementsR

namespace PalomarCorpus.E1041.PaperStatementsK
open Finset
/-- States res:critical-proximity from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_two_roots_dist_sum_le_two_mul_geomMean
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  sorry
end PalomarCorpus.E1041.PaperStatementsK

namespace PalomarCorpus.E1041.PaperStatementsB
open Finset
open Polynomial
open scoped BigOperators
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.exists_two_nearest_roots_of_polynomial_critical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0) :
    ∃ i j : Fin n, i ≠ j ∧
      (∀ k, ‖c - z i‖ ≤ ‖c - z k‖) ∧
      (∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) ∧
      ‖c - z i‖ + ‖c - z j‖ < 2 := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.two_nearest_roots_of_polynomial_critical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, ‖c - z i‖ ≤ ‖c - z k‖)
    (hj : ∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) :
    ‖c - z i‖ + ‖c - z j‖ < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsB

namespace PalomarCorpus.E1041.PaperStatementsG
open Polynomial
/-- States res:straight-no-go from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperStraightObstructions.complete_straight_path_obstructions in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complete_straight_path_obstructions :
    (∃ f : ℂ[X], f.Monic ∧ f.natDegree = 5 ∧
      (∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1) ∧
      ∃ c w : ℂ, f.derivative.eval c = 0 ∧ f.eval c ≠ 0 ∧ f.eval w = 0 ∧
        (∀ z : ℂ, f.eval z = 0 → z ≠ w → ‖c - w‖ < ‖c - z‖) ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 < ‖f.eval (c + (t : ℂ) * (w - c))‖) ∧
    (∃ g : ℂ[X], g.Monic ∧ g.natDegree = 3 ∧
      (∀ z : ℂ, g.eval z = 0 → ‖z‖ < 1) ∧
      ∀ z w : ℂ, g.eval z = 0 → g.eval w = 0 → z ≠ w →
        1 < ‖g.eval ((z + w) / 2)‖) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsG

namespace PalomarCorpus.E1041.PaperStatementsU
open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_05.Shared (ConnectedBelow)
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
/-- A specified two-segment connector, rather than merely existence of some rectifiable curve. The public `hub` fixes its image and parametrisation. Local copy of ErdosProblems.Erdos1041.PaperCurve.HubBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HubBelow (f : ℂ → ℂ) (R L : ℝ) (a h b : ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 2, ‖f (hub a h b t)‖ < R) ∧
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
/-- States res:primitive-quintic from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complete_primitive_quintic (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z)
    (hdisk : ∀ z, p.eval z = 0 → ‖z‖ < 1) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ∃ i j : Fin 5, i ≠ j ∧ ‖b*w i+c‖ < 1 ∧ ‖b*w j+c‖ < 1 ∧
        ConnectedBelow p.eval 1 2 (w i) (w j) ∧
        (w i ≠ w j → HubBelow p.eval 1 2 (w i) 0 (w j)) ∧
        (w i = w j →
          (∀ t : ℝ, ‖p.eval ((fun _ : ℝ => w i) t)‖ < 1) ∧
          eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsU

namespace PalomarCorpus.E1041.PaperStatementsZA
open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_05.Shared (ConnectedBelow)
/-- A closed sublevel connector, allowing the zero-length repeated-root case. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ConnectedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.HasDistinctConnection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootsInOpenUnitDisc, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootsInOpenUnitDisc (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1
/-- The paper's normalised critical-value separation at a real centre `w₀`: every OTHER critical point `d` satisfies `|f(d)/f(c) - w₀| ≥ S`. For `w₀ = 1` this is `ConnectorR18.ValueSeparatedAt`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.ValueSeparatedAtCentre, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ValueSeparatedAtCentre (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ) : Prop :=
  ∀ d : ℂ, f.derivative.eval d = 0 → d ≠ c → S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖
/-- The right side of the paper's displayed bound `eq:disk-family-length`, without the `2|v|^{2/n}` prefactor: `(S/(n-1))^{2/n} log((S² + S + p)/(S² - S + p))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separationCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def separationCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))
/-- **The external analytic input**: the paper's Theorem `res:critical-value-separation` (separation of one simple critical value). `f` monic of degree `n ≥ 3`, `c` a simple critical point with `v = f(c) ≠ 0`, `w₀ ∈ [0,1]`, `S > max(w₀, 1-w₀)`, and every other critical point `d` obeying `|f(d)/v - w₀| ≥ S`; then two distinct roots are joined inside `{|f| ≤ |v|}` by a curve `Γ` with `length(Γ)² ≤ 2|v|^{2/n}(S/(n-1))^{2/n} log((S²+S+p)/(S²-S+p))`, `p = w₀(1-w₀)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.CriticalValueSeparationTheorem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalValueSeparationTheorem : Prop :=
  ∀ (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ), f.Monic → 3 ≤ f.natDegree →
    f.derivative.eval c = 0 → f.derivative.derivative.eval c ≠ 0 →
    f.eval c ≠ 0 → 0 ≤ w₀ → w₀ ≤ 1 → max w₀ (1 - w₀) < S →
    ValueSeparatedAtCentre f c w₀ S →
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ConnectedAtMost f.eval ‖f.eval c‖
        (Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
          separationCoefficient f.natDegree S (w₀ * (1 - w₀)))) a b
/-- States res:separation-parent from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem separation_parent (hSep : CriticalValueSeparationTheorem)
    {f : ℂ[X]} {c : ℂ} {w₀ S : ℝ}
    (hmonic : f.Monic) (hdeg : 3 ≤ f.natDegree)
    (hroots : RootsInOpenUnitDisc f)
    (hcrit : f.derivative.eval c = 0) (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv0 : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw0 : 0 ≤ w₀) (hw1 : w₀ ≤ 1) (hS : 4 / 3 ≤ S)
    (hsep : ValueSeparatedAtCentre f c w₀ S) :
    HasDistinctConnection f 1 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsZA

namespace PalomarCorpus.E1041.PaperStatementsQ
open Set
open Metric
open AffineSubspace
open Polynomial
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.P, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def P : ℂ[X] := X ^ 3 + (C (3 / 100 : ℂ) * X ^ 1 + C (-3 / 4 : ℂ))
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.minus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def minus : ℂ := -Complex.I / 10
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.plus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def plus : ℂ := Complex.I / 10
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.mu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mu : ℝ := ‖P.eval plus‖
/-- Two complex values lie on the same oriented ray from the origin. Local copy of ErdosProblems.Erdos1041.SamePositiveRay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a
/-- States res:sep-or-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complete_sep_or_counterexample :
    P.Monic ∧ P.natDegree = 3 ∧
    (∀ z : ℂ, P.eval z = 0 → ‖z‖ < 1) ∧
    (∀ z : ℂ, P.derivative.eval z = 0 ↔ z = plus ∨ z = minus) ∧
    plus ≠ minus ∧
    (∀ z : ℂ, P.derivative.eval z = 0 → P.derivative.derivative.eval z ≠ 0) ∧
    IsLeast {x : ℝ | ∃ c : ℂ, P.derivative.eval c = 0 ∧ x = ‖P.eval c‖} mu ∧
    (13 / 25 : ℝ) < mu ∧
    ¬ SamePositiveRay (P.eval plus) (P.eval minus) ∧
    ‖1 - P.eval minus / P.eval plus‖ < (2 / 375 : ℝ) ∧
    (2 / 375 : ℝ) < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsQ

namespace PalomarCorpus.E1041.PaperStatementsX
open Polynomial
open Set
export PalomarCorpus.E1041_05.Shared (lobeComponent lobePolynomial lobeSublevel)
/-- The external classical input for the perimeter clause: for a bounded planar set containing a closed disc of radius `ρ`, the one-dimensional Hausdorff measure of the boundary is at least the circumference `2πρ`. This is absent from Mathlib (which has `μH[1]` but no perimeter-monotonicity or isoperimetric inequality) and from this tree. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.PlanePerimeterBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PlanePerimeterBound : Prop :=
  ∀ (A : Set ℂ) (x : ℂ) (ρ : ℝ), 0 ≤ ρ → Bornology.IsBounded A →
    Metric.closedBall x ρ ⊆ A →
    ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (frontier A)
/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobe_perimeter_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lobe_perimeter_gt (hperim : PlanePerimeterBound) :
    ENNReal.ofReal (5 * Real.pi / 4)
      < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) := by
  sorry
/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_root_gamma_false (hperim : PlanePerimeterBound)
    (hGammaQuarter : Real.Gamma (1 / 4) ≤ 3.63) :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsX

namespace PalomarCorpus.E1041.PaperStructuresAD
open Polynomial
open Set
export PalomarCorpus.E1041_05.Shared (lobeComponent lobePolynomial lobeSublevel)
/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_root_gamma_false_unconditional :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := by
  sorry
end PalomarCorpus.E1041.PaperStructuresAD
