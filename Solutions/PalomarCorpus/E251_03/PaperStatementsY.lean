/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.NonconcentrationConsequencesR11
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR21.TwoWindowSparsity
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail
import Solutions.PalomarCorpus.E251_03.Statement

open scoped BigOperators
open Filter
open Topology
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsY
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)

theorem prime_gap_equal_shift_zeroDensity (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := @ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity h hh hSP

theorem prime_gap_two_window_sparse (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | 1 ≤ N ∧
        (-1 < shift realPrimeGapTail h N ∧ shift realPrimeGapTail h N < 1) ∧
        (-1 < shift realPrimeGapTail h (N + 1) ∧
          shift realPrimeGapTail h (N + 1) < 1) ∧
        (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ)} ∧
      ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)} := @ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse h hh hSP

end PalomarCorpus.E251.PaperStatementsY
