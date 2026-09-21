/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243j

Every non-theorem declaration of `PalomarCorpus/E243j/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
open scoped Topology
open MeasureTheory

namespace PalomarCorpus.E243.PaperStatementsJ
open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
open scoped Topology
open MeasureTheory
/-- For a nonnegative locally integrable function this is the usual statement that the improper integral from one to infinity is +∞. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.realCutoffPrefixMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realCutoffPrefixMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if (u j : ℝ) ≤ X then w j else 0
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.RealPrefixLowerDensityZero, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealPrefixLowerDensityZero (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  Filter.liminf (fun X : ℝ => realCutoffPrefixMass u w X / ENNReal.ofReal X) atTop = 0
end PalomarCorpus.E243.PaperStatementsJ
