/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets`,
`ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightMixedClaim`,
`ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBO

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

/-- States res:mixed-supports, thm:257-mixed-supports from the long record and the short record
for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBO
