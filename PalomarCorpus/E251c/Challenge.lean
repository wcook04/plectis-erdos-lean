/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band c

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Finset
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E251.PaperStatementsC
open Filter
open Finset
open scoped BigOperators
open scoped Topology
/-- Local copy of ErdosProblems.Erdos251.PaperCompleteR20.realDyadicTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realDyadicTail (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, a (N + j + 1) / 2 ^ (j + 1)
/-- States long251:res:true-tail, res:true-tail from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E251.PaperStatementsC
