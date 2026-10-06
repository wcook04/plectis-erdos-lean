/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

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
`ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets`,
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

/-- States thm:periodic-support from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_erdosSupportSeries_positivePeriodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := by
  sorry

/-- States res:terminalhalf from the short record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf_iff in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_terminalhalf_iff :
    (∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧ erdosSupportSeries 2 B = (1 : ℝ) / 2) ↔
      ∃ (M : ℕ → ℕ) (A : ℕ → Set ℕ),
        (∀ j, 1 ≤ M j) ∧
          Filter.Tendsto M Filter.atTop Filter.atTop ∧
          (∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j) ∧
          Filter.Tendsto
            (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
            Filter.atTop (nhds 0) := by
  sorry

/-- States prop:257-finite-witness-rule from the long record for Erdős problem #257. Transported
from ErdosProblems.Erdos257.finite_monotone_witness_rule_realised in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCO
