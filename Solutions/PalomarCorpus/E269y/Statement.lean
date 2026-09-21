/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269y

Every non-theorem declaration of `PalomarCorpus/E269y/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsY
open Polynomial
open scoped BigOperators
/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`. The outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.heckeMahlerSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k
/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at nonzero algebraic arguments inside the stated region. This is the one external input of the two-prime theorem. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.BugeaudLaurentTranscendence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. Local copy of ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊
end PalomarCorpus.E269.PaperStatementsY
