/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision
import Solutions.PalomarCorpus.E257ai.Statement

open Filter
open Topology
open Classical

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAI

theorem paper_forced_greedy_low_ranks {J : ℕ} (hJ : 2 ≤ J) :
    (1 ∉ rungGreedySupport J ∧ rungRem J 1 ≤ rungTail J 1) ∧
      2 ∈ rungGreedySupport J ∧ 3 ∈ rungGreedySupport J := @ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_low_ranks J hJ

end PalomarCorpus.E257.PaperStatementsAI
