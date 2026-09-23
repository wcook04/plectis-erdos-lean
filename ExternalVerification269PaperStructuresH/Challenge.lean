/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.PaperR7FiniteCutRank`.
-/

open scoped BigOperators
open Module
open Submodule

namespace Erdos249257.ExternalVerification269PaperStructuresH

noncomputable def cutVector {F : Type*} [Field F] (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c

/-- States long269:res:finite-cut-rank, res:finite-cut-rank from the long record and the short
record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR7.rank_cutMatrix in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by
  sorry

end Erdos249257.ExternalVerification269PaperStructuresH
