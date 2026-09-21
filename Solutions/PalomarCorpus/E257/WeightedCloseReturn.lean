/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import Solutions.PalomarCorpus.E257.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E257.WeightedCloseReturn
export PalomarCorpus.E257.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)

theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε := by
  simpa only [erdosSupportSeries, primeSetPart, primeWeightedTerm, FinitePrimeWeighted, shiftedRadixAtom, shiftedRadixSupportAtom, displacement, Erdos257PeriodNoncollapse.erdosSupportSeries, Erdos257PeriodNoncollapse.shiftedRadixAtom, Erdos257PeriodNoncollapse.shiftedRadixSupportAtom, ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.displacement] using
    ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return b E hb hE0 hE hInf ε hε N

end PalomarCorpus.E257.WeightedCloseReturn
end
