/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusLocalRepair
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import Solutions.PalomarCorpus.E257_33.Statement

open scoped BigOperators
open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAX
export PalomarCorpus.E257_33.Shared (ExactLocalMersenneHalfRow localMersenneQuotient localPrefixQuotient)

theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle n hn hrow

theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_example_six_and_eleven

theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_returning_endpoint_may_fail_to_grow

end PalomarCorpus.E257.PaperStatementsAX
