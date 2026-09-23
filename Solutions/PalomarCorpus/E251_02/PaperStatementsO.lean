/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperTailBoundsR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail
import Solutions.PalomarCorpus.E251_02.Statement

open Filter
open Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsO
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)

theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N)) := @ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate h N L

end PalomarCorpus.E251.PaperStatementsO
