/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041u

Every non-theorem declaration of `PalomarCorpus/E1041u/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E1041.PaperStatementsU
open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
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
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
end PalomarCorpus.E1041.PaperStatementsU
