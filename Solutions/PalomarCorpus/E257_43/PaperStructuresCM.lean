/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision
import Solutions.PalomarCorpus.E257_43.Statement

open Filter
open Topology
open Classical

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCM
export PalomarCorpus.E257_43.Shared (rungTail rungWeight)

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

end PalomarCorpus.E257.PaperStructuresCM
