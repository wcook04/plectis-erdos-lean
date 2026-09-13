/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import Solutions.PalomarCorpus.E257.Statement

open Set

namespace PalomarCorpus.E257.DivisibilityWeightedSupport
export PalomarCorpus.E257.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)

noncomputable section

theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

theorem primeSetPart_eq :
    primeSetPart = ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart := rfl

theorem primeWeightedTerm_eq :
    primeWeightedTerm = ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm := by
  funext b P a
  simp [primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm,
    primeSetPart_eq]

theorem FinitePrimeWeighted_eq :
    FinitePrimeWeighted = ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted := by
  funext b A
  simp [FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted,
    primeWeightedTerm_eq]

theorem DivisibilityWeightedClaim_eq :
    DivisibilityWeightedClaim =
      ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim := by
  unfold DivisibilityWeightedClaim
    ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim
  rw [FinitePrimeWeighted_eq, erdosSupportSeries_eq]

theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  rw [DivisibilityWeightedClaim_eq]
  exact ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim

end

end PalomarCorpus.E257.DivisibilityWeightedSupport
