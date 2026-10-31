/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientShiftedMobiusPulse
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion
import Solutions.PalomarCorpus.E249_15.Statement

open ArithmeticFunction
open scoped BigOperators
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBM
export PalomarCorpus.E249_15.Shared (forwardMultipleQuotient forwardMultipleShift totientTail)

theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion N

end PalomarCorpus.E249.PaperStatementsBM
