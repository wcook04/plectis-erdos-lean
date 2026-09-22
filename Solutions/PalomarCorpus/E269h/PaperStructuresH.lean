/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperR7FiniteCutRank
import Solutions.PalomarCorpus.E269h.Statement

open scoped BigOperators
open Module
open Submodule

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStructuresH

theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := @ErdosProblems.Erdos269.PaperR7.rank_cutMatrix F inferInstance ι inferInstance c hc0 hc1 m hm E hbound A hcols

end PalomarCorpus.E269.PaperStructuresH
