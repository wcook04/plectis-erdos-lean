/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR11.IntegralWeights
import ErdosProblems.Erdos243.PaperCompleteR20.RealCutoffCriterion

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.IntegralWeights`,
`ErdosProblems.Erdos243.PaperCompleteR20.RealCutoffCriterion`.
-/

open Filter
open Set
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
open scoped Topology
open MeasureTheory

namespace Erdos249257.ExternalVerification243PaperStatementsJ

noncomputable def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t

noncomputable def realCutoffPrefixMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if (u j : ℝ) ≤ X then w j else 0

noncomputable def RealPrefixLowerDensityZero (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  Filter.liminf (fun X : ℝ => realCutoffPrefixMass u w X / ENNReal.ofReal X) atTop = 0

theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := @ErdosProblems.Erdos243.PaperCompleteR20.real_lowerDensityZero_iff_exists_admissible_real_weight u w hu

end Erdos249257.ExternalVerification243PaperStatementsJ
