/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.QuantitativeSelectorEscape
import Solutions.PalomarCorpus.E1049_06.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresP

noncomputable instance instDecidableEqReal_erdosProblems : DecidableEq ℝ := Classical.decEq ℝ

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
      0 < |g x - g y| ∧ |g x - g y| < δ := @ErdosProblems.Erdos1049.exists_small_real_escape_of_conditional_multiplicity α β ι inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance f g bin k δ hg hdiam hcard

end PalomarCorpus.E1049.PaperStructuresP
