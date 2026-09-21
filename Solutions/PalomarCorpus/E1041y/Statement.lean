/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041y

Every non-theorem declaration of `PalomarCorpus/E1041y/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open scoped NNReal
open scoped ENNReal
open scoped BigOperators

namespace PalomarCorpus.E1041.PaperStatementsY
open Polynomial
open scoped NNReal
open scoped ENNReal
open scoped BigOperators
/-- Two zero occurrences joined by a path of length at most `L` inside the OPEN sublevel set `{|f| < R}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaJoinedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
/-- **External input for `res:constant-factor-capacity`.** The averaging proof of `res:constant-factor-path`, rerun on the component `C` of `{|f| < 2μ}` containing the first-merge critical point, with the global area input replaced by the component form `Area(C) ≤ π cap(closure C)² = π κ²(2μ)^{2/n}` of the area–capacity inequality, at `λ = 2`, `r = 1/20`. `κ` is the paper's capacity ratio `cap(closure C)/(2μ)^{1/n}`; the pinned Mathlib has no logarithmic capacity, so `κ` enters as the real parameter this hypothesis is stated for. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CFACapacityConstruction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CFACapacityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (κ : ℝ) (k₀ : ℕ) : Prop :=
  cfaJoinedBelow f z 1
    (Real.sqrt (2 / (k₀ : ℝ)) *
      (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
        κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))))
/-- The paper's `A = 283/3610` and `B = 52029/9100`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaA, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaA : ℝ := 283 / 3610
/-- Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaB, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaB : ℝ := 52029 / 9100
/-- The paper's threshold `τ_k = (√(2k) - A)/B`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaTau (k : ℕ) : ℝ := (Real.sqrt (2 * (k : ℝ)) - cfaA) / cfaB
end PalomarCorpus.E1041.PaperStatementsY
