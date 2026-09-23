/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCompleteR20.TrueTail
import Solutions.PalomarCorpus.E251_01.Statement

open Filter
open Finset
open scoped BigOperators
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsC

theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0) := @ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff a U habs hrec

end PalomarCorpus.E251.PaperStatementsC
