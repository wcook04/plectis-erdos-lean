/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041d

Every non-theorem declaration of `PalomarCorpus/E1041d/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open scoped ENNReal
open scoped NNReal

namespace PalomarCorpus.E1041.PaperStatementsD
open Set
open scoped ENNReal
open scoped NNReal
/-- `π/n`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.angle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def angle (n : ℕ) : ℝ := Real.pi / (n : ℝ)
/-- `c = cos(π/n)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordCos (n : ℕ) : ℝ := Real.cos (angle n)
/-- `ε = (1 - r^n)^{1/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordEps, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordEps (n : ℕ) (r : ℝ) : ℝ := (1 - r ^ n) ^ ((n : ℝ)⁻¹)
/-- `e^{iπ/n}`; its square is the paper's `ω = e^{2πi/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.halfRoot, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfRoot (n : ℕ) : ℂ := Complex.exp ((angle n : ℂ) * Complex.I)
/-- `ω = e^{2πi/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordOmega, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordOmega (n : ℕ) : ℂ := halfRoot n ^ 2
/-- The point of the segment `[s, sω]` at parameter `u ∈ [0,1]`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordPoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordPoint (n : ℕ) (s u : ℝ) : ℂ :=
  (s : ℂ) * (((1 - u : ℝ) : ℂ) + ((u : ℝ) : ℂ) * chordOmega n)
/-- `r_* = (1 + c^n)^{-1/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordThreshold (n : ℕ) : ℝ := (1 + chordCos n ^ n) ^ (-((n : ℝ)⁻¹))
/-- The paper's inner radius `t = ε/c`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.innerRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def innerRadius (n : ℕ) (r : ℝ) : ℝ := chordEps n r / chordCos n
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
end PalomarCorpus.E1041.PaperStatementsD
