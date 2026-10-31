/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_04

Every non-theorem declaration of `PalomarCorpus/E1041_04/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
open scoped ComplexConjugate
open Real
open Filter
open Metric
open Bornology
open scoped Topology
open AffineSubspace

namespace PalomarCorpus.E1041_04.Shared
/-- The family `c` indexed by `Fin (n - 1)` lists the critical points of `p` with multiplicity: the derivative of `p` equals `C (n : ℂ)` times the product over `j` of `X - C (c j)`. For a monic `p` of degree `n` this says that `c` enumerates the `n - 1` zeros of the derivative, each as often as its multiplicity. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Every zero of the complex polynomial `p` lies in the closed disc of radius `R` about `h`: `p.eval z = 0` implies `‖z - h‖ ≤ R`. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- Two complex values lie on the same oriented ray from the origin. Local copy of ErdosProblems.Erdos1041.SamePositiveRay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
end PalomarCorpus.E1041_04.Shared

namespace PalomarCorpus.E1041.PaperStatementsM
end PalomarCorpus.E1041.PaperStatementsM

namespace PalomarCorpus.E1041.PaperStatementsU
open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_04.Shared (rootProduct value)
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
/-- A specified two-segment connector, rather than merely existence of some rectifiable curve. The public `hub` fixes its image and parametrisation. Local copy of ErdosProblems.Erdos1041.PaperCurve.HubBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HubBelow (f : ℂ → ℂ) (R L : ℝ) (a h b : ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 2, ‖f (hub a h b t)‖ < R) ∧
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal L
end PalomarCorpus.E1041.PaperStatementsU

namespace PalomarCorpus.E1041.PaperStatementsV
open Polynomial
open Set
open scoped BigOperators
export PalomarCorpus.E1041_04.Shared (rootProduct value)
end PalomarCorpus.E1041.PaperStatementsV

namespace PalomarCorpus.E1041.PaperStatementsJ
open scoped ComplexConjugate
end PalomarCorpus.E1041.PaperStatementsJ

namespace PalomarCorpus.E1041.PaperStatementsO
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
end PalomarCorpus.E1041.PaperStatementsO

namespace PalomarCorpus.E1041.PaperStatementsP
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
open Real
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
/-- Local copy of ErdosProblems.Erdos1041.radialEqualityPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def radialEqualityPolynomial (n : ℕ) (h lam : ℂ) : ℂ[X] := (X - C h) ^ n - C lam
end PalomarCorpus.E1041.PaperStatementsP

namespace PalomarCorpus.E1041.PaperStatementsW
open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
/-- Reflected-derivative bound, with the derivative root multiplicities specified by an exact polynomial factorisation. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ReflectedCriticalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖
end PalomarCorpus.E1041.PaperStatementsW

namespace PalomarCorpus.E1041.PaperStatementsQ
open Set
open Metric
open AffineSubspace
open Polynomial
export PalomarCorpus.E1041_04.Shared (SamePositiveRay)
/-- The complex Newton vector associated with a value and its nonzero derivative. Local copy of ErdosProblems.Erdos1041.newtonFlowVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def newtonFlowVector (value derivative : ℂ) : ℂ :=
  -value / derivative
end PalomarCorpus.E1041.PaperStatementsQ

namespace PalomarCorpus.E1041.PaperStatementsN
open Set
open Metric
open AffineSubspace
open Polynomial
export PalomarCorpus.E1041_04.Shared (SamePositiveRay)
end PalomarCorpus.E1041.PaperStatementsN
