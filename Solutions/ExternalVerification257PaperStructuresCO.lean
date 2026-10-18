/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR20.PositivePeriodicSupport
import ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR7.PrimeWeightedDefinitions
import ErdosProblems.Erdos257.WitnessLogicIrrational

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`,
`ErdosProblems.Erdos257.PaperCompleteR20.PositivePeriodicSupport`,
`ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence`,
`ErdosProblems.Erdos257.PaperCompleteR7.PrimeWeightedDefinitions`,
`ErdosProblems.Erdos257.WitnessLogicIrrational`.
-/

open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresCO

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def terminalPaperCarry (A : Set ℕ) (M : ℕ) : ℤ :=
  (2 : ℤ) ^ (M - 1) -
    ∑ j ∈ Finset.range (M - 1),
      (2 : ℤ) ^ (M - 2 - j) * (supportCoeff A (j + 2) : ℤ)

noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

theorem irrational_erdosSupportSeries_positivePeriodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := by
  first
  | exact @ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic b m A hb hm hper hpos
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic b m A hb hm hper hpos
    done
  | apply ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic <;> assumption
    done
  | simpa only [erdosSupportSeries, primeSetPart, primeWeightedTerm, supportCoeff, terminalPaperCarry] using ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic b m A hb hm hper hpos
    done
  | with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic b m A hb hm hper hpos
    done

theorem paper_terminalhalf_iff :
    (∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧ erdosSupportSeries 2 B = (1 : ℝ) / 2) ↔
      ∃ (M : ℕ → ℕ) (A : ℕ → Set ℕ),
        (∀ j, 1 ≤ M j) ∧
          Filter.Tendsto M Filter.atTop Filter.atTop ∧
          (∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j) ∧
          Filter.Tendsto
            (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
            Filter.atTop (nhds 0) := by
  first
  | exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff
    done
  | apply ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff <;> assumption
    done
  | simpa only [erdosSupportSeries, primeSetPart, primeWeightedTerm, supportCoeff, terminalPaperCarry] using ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff
    done
  | with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff
    done

theorem finite_monotone_witness_rule_realised
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∃ H : Set ℕ, 0 ∉ H ∧
      (∀ b : ℕ, 2 ≤ b → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
        (Summable (Set.indicator H (primeWeightedTerm b P)) ↔ U (P ∩ E))) ∧
      ¬ Summable (Set.indicator H (fun a : ℕ => (1 : ℝ) / a)) ∧
      (∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)) := by
  first
  | exact @ErdosProblems.Erdos257.finite_monotone_witness_rule_realised E hE U hUp hUE hU0
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos257.finite_monotone_witness_rule_realised E hE U hUp hUE hU0
    done
  | apply ErdosProblems.Erdos257.finite_monotone_witness_rule_realised <;> assumption
    done
  | simpa only [erdosSupportSeries, primeSetPart, primeWeightedTerm, supportCoeff, terminalPaperCarry] using ErdosProblems.Erdos257.finite_monotone_witness_rule_realised
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos257.finite_monotone_witness_rule_realised E hE U hUp hUE hU0
    done
  | with_unfolding_all exact @ErdosProblems.Erdos257.finite_monotone_witness_rule_realised E hE U hUp hUE hU0
    done

end Erdos249257.ExternalVerification257PaperStructuresCO
