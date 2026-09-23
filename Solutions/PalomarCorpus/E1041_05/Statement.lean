/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_05

Every non-theorem declaration of `PalomarCorpus/E1041_05/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1041.PaperStatementsR

namespace PalomarCorpus.E1041.PaperStatementsK
open Finset
end PalomarCorpus.E1041.PaperStatementsK

namespace PalomarCorpus.E1041.PaperStatementsB
open Finset
open Polynomial
open scoped BigOperators
end PalomarCorpus.E1041.PaperStatementsB

namespace PalomarCorpus.E1041.PaperStatementsG
open Polynomial
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
end PalomarCorpus.E1041.PaperStatementsX

namespace PalomarCorpus.E1041.PaperStructuresAD
open Polynomial
open Set
export PalomarCorpus.E1041_05.Shared (lobeComponent lobePolynomial lobeSublevel)
end PalomarCorpus.E1041.PaperStructuresAD
