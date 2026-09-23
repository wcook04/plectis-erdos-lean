/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.QuantitativeSelectorEscape`.
-/

namespace Erdos249257.ExternalVerification1049PaperStructuresP

noncomputable instance instDecidableEqReal_erdosProblems : DecidableEq ℝ := Classical.decEq ℝ

/-- States res:boundedfibre from the short record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.exists_small_real_escape_of_conditional_multiplicity in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_small_real_escape_of_conditional_multiplicity
    {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (g : α → ℝ) (bin : α → ι) (k : ℕ) (δ : ℝ)
    (hg : ∀ x : α,
      (Finset.univ.filter fun y => f y = f x ∧ g y = g x).card ≤ k)
    (hdiam : ∀ x y : α, bin x = bin y → |g x - g y| < δ)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧
      0 < |g x - g y| ∧ |g x - g y| < δ := by
  sorry

end Erdos249257.ExternalVerification1049PaperStructuresP
