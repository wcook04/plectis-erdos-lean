/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision`.
-/

open Filter
open Topology
open Classical

namespace Erdos249257.ExternalVerification257PaperStructuresCM

noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))

noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)

theorem paper_forced_greedy_tail_lt_weight' {J : ℕ} (hJ : 2 ≤ J) (n : ℕ) :
    rungTail J n < rungWeight J n := by
  first
  | (exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight' J hJ n; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight' J hJ n; done)
  | (apply ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight' <;> assumption; done)
  | (simpa only [rungTail, rungWeight] using ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight'; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight' J hJ n; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight' J hJ n; done)

end Erdos249257.ExternalVerification257PaperStructuresCM
