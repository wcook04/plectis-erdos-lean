/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail
import Solutions.PalomarCorpus.E251l.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsL

theorem actual_free_pair_criterion :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral realPrimeGapTail := @ErdosProblems.Erdos251.PaperR7.actual_free_pair_criterion

end PalomarCorpus.E251.PaperStatementsL
