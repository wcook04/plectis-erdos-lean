/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269, band h

Erdős problem #269 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E269` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Module
open Submodule

namespace PalomarCorpus.E269.PaperStructuresH
open scoped BigOperators
open Module
open Submodule
/-- A cut at `k`, with `m` rows. Local copy of ErdosProblems.Erdos269.PaperR7.cutVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cutVector {F : Type*} [Field F] (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c
/-- States long269:res:finite-cut-rank, res:finite-cut-rank from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.rank_cutMatrix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by
  sorry
end PalomarCorpus.E269.PaperStructuresH
