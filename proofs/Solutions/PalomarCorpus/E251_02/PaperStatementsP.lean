/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail
import Solutions.PalomarCorpus.E251_02.Statement

open scoped BigOperators
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsP
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)

theorem finite_small_pair :
    (-1 < realTailShift realPrimeGapTail 1 2 ∧
      realTailShift realPrimeGapTail 1 2 < 1) ∧
    (-1 < realTailShift realPrimeGapTail 1 3 ∧
      realTailShift realPrimeGapTail 1 3 < 1) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 2) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 3) ∧
    primeGap0 4 = 2 ∧ primeGap0 3 = 4 := @ErdosProblems.Erdos251.PaperR7.finite_small_pair

end PalomarCorpus.E251.PaperStatementsP
