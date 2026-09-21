/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR20.SparseNonconcentration
import Solutions.PalomarCorpus.E251k.Statement

open Filter
open Topology
open Finset
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsK

theorem sparse_nonconcentration (a b : ℕ → ℤ) (S : Set ℕ)
    (hS : ZeroDensity S) (hab : ∀ n, n ∉ S → a n = b n)
    (ha : FixedBlockNonconcentration a) : FixedBlockNonconcentration b := @ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration a b S hS hab ha

end PalomarCorpus.E251.PaperStatementsK
