/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249am

Every non-theorem declaration of `PalomarCorpus/E249am/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped Classical

namespace PalomarCorpus.E249.PaperStatementsAM
open scoped Classical
/-- `x` is nondyadic. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.NotDyadicRational, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j
/-- `‖x‖_{ℝ/ℤ} ≥ 1/4`, written as: every integer is at distance at least `1/4` from `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.QuarterFarFromInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|
/-- The `k`-th binary digit of `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.binaryDigitAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2
/-- `α_h = (2^h - 1) S`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientAlphaShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
/-- The number of `N ∈ [X, 2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseCount (h X : ℕ) : ℕ :=
  ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h)).card
/-- `ρ_h(X)`: the proportion of `N ∈ [X,2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseProportion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseProportion (h X : ℕ) : ℝ := (quarterFarPhaseCount h X : ℝ) / (X : ℝ)
end PalomarCorpus.E249.PaperStatementsAM
