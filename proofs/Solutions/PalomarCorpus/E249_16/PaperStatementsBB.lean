/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientMahlerDefect
import ErdosProblems.Erdos249.PaperCompleteR21.CanonicalDyadicSectionRank
import ErdosProblems.Erdos249.PaperCompleteR21.DyadicSectionBasisAndRationalCarry
import Solutions.PalomarCorpus.E249_16.Statement

open Module
open Matrix

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBB

noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ) := @ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries e

theorem canonicalTotientKernelFamily_independent_card_and_span (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Function.Injective (canonicalTotientKernelFamily e) ∧
      Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))
        = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
      ¬ FiniteDimensional ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := @ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span e he

theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level e he

theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2 := @ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels

theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index e

theorem completeLevelZeroTruncation_is_totient_and_rank_one :
    Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := @ErdosProblems.Erdos249.PaperCompleteR21.completeLevelZeroTruncation_is_totient_and_rank_one

theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := @ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one

theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) := @ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family e

theorem retainedSections_basis_and_rank (e : ℕ) (he : 1 ≤ e) :
    (∃ b : Module.Basis (TotientCanonicalIndex e) ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))),
        ∀ i, (b i : ℕ → ℚ) = canonicalTotientKernelFamily e i) ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
        = 2 ^ e + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.retainedSections_basis_and_rank e he

end PalomarCorpus.E249.PaperStatementsBB
