/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.PaperCompleteR20.TrueTail

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperCompleteR20.TrueTail`.
-/

open Filter
open Finset
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification251PaperStatementsC

noncomputable def realDyadicTail (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, a (N + j + 1) / 2 ^ (j + 1)

theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0) := @ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff a U habs hrec

end Erdos249257.ExternalVerification251PaperStatementsC
