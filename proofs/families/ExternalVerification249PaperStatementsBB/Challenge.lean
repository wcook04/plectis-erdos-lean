/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TotientMahlerDefect`,
`ErdosProblems.Erdos249.PaperCompleteR21.CanonicalDyadicSectionRank`,
`ErdosProblems.Erdos249.PaperCompleteR21.DyadicSectionBasisAndRationalCarry`.
-/

open Module
open Matrix

namespace Erdos249257.ExternalVerification249PaperStatementsBB

noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem canonicalTotientKernelFamily_independent_card_and_span (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Function.Injective (canonicalTotientKernelFamily e) ∧
      Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))
        = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
      ¬ FiniteDimensional ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := by
  sorry

/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  sorry

/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2 := by
  sorry

/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.completeLevelZeroTruncation_is_totient_and_rank_one
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem completeLevelZeroTruncation_is_totient_and_rank_one :
    Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := by
  sorry

/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := by
  sorry

/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.retainedSections_basis_and_rank in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem retainedSections_basis_and_rank (e : ℕ) (he : 1 ≤ e) :
    (∃ b : Module.Basis (TotientCanonicalIndex e) ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))),
        ∀ i, (b i : ℕ → ℚ) = canonicalTotientKernelFamily e i) ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
        = 2 ^ e + 1 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBB
