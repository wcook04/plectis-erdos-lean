/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band j

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
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
/-- States res:weights from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.real_lowerDensityZero_iff_exists_admissible_real_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsJ
