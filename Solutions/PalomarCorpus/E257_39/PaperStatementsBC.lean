/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR21.ResidueClassSupport
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedHereditaryClaim
import Solutions.PalomarCorpus.E257_39.Statement

open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsBC
export PalomarCorpus.E257_39.Shared (erdosSupportSeries supportCoeff)

theorem paper_terminalhalf
    (M : ℕ → ℕ) (A : ℕ → Set ℕ)
    (hM : ∀ j, 1 ≤ M j)
    (hlim : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hA : ∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j)
    (herr : Filter.Tendsto
      (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
      Filter.atTop (nhds 0)) :
    ∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧
      erdosSupportSeries 2 B = (1 : ℝ) / 2 := @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf M A hM hlim hA herr

theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}) := @ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support b m c hb hm

theorem finitePrimeWeighted_fixedBase_hereditary
    (b : ℕ) (H : Set ℕ) (hb : 2 ≤ b) (hH0 : 0 ∉ H)
    (hH : FinitePrimeWeighted b H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      Irrational (erdosSupportSeries b A) := @ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary b H hb hH0 hH

end PalomarCorpus.E257.PaperStatementsBC
