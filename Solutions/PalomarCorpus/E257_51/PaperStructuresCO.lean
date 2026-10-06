/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR20.PositivePeriodicSupport
import ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.WitnessLogicIrrational
import Solutions.PalomarCorpus.E257_51.Statement

open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCO
export PalomarCorpus.E257_51.Shared (erdosSupportSeries primeSetPart primeWeightedTerm)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def terminalPaperCarry (A : Set ℕ) (M : ℕ) : ℤ :=
  (2 : ℤ) ^ (M - 1) -
    ∑ j ∈ Finset.range (M - 1),
      (2 : ℤ) ^ (M - 2 - j) * (supportCoeff A (j + 2) : ℤ)

theorem irrational_erdosSupportSeries_positivePeriodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := @ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic b m A hb hm hper hpos

theorem paper_terminalhalf_iff :
    (∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧ erdosSupportSeries 2 B = (1 : ℝ) / 2) ↔
      ∃ (M : ℕ → ℕ) (A : ℕ → Set ℕ),
        (∀ j, 1 ≤ M j) ∧
          Filter.Tendsto M Filter.atTop Filter.atTop ∧
          (∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j) ∧
          Filter.Tendsto
            (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
            Filter.atTop (nhds 0) := @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff

theorem finite_monotone_witness_rule_realised
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∃ H : Set ℕ, 0 ∉ H ∧
      (∀ b : ℕ, 2 ≤ b → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
        (Summable (Set.indicator H (primeWeightedTerm b P)) ↔ U (P ∩ E))) ∧
      ¬ Summable (Set.indicator H (fun a : ℕ => (1 : ℝ) / a)) ∧
      (∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)) := @ErdosProblems.Erdos257.finite_monotone_witness_rule_realised E hE U hUp hUE hU0

end PalomarCorpus.E257.PaperStructuresCO
