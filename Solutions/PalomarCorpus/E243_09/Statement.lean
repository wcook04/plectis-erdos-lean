/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_09

Every non-theorem declaration of `PalomarCorpus/E243_09/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E243.PaperStatementsA
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. Local copy of ErdosProblems.Erdos243.nextDenState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. Local copy of ErdosProblems.Erdos243.nextTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- The next denominator defect from the Sylvester step. Local copy of ErdosProblems.Erdos243.sylvesterDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsS
open Filter
/-- Cumulative least common multiple of the initial denominator and all digits strictly before `n`. Local copy of ErdosProblems.Erdos243.cumulativeDigitLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.lcmDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
end PalomarCorpus.E243.PaperStatementsS

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
