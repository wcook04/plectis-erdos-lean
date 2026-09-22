/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision`.
-/

open Filter
open Topology
open Classical

namespace Erdos249257.ExternalVerification257PaperStatementsJ

noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)

noncomputable def rungSupportWeight (J : ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A then rungWeight J n else 0

noncomputable def HalfRung (J : ℕ) : Prop :=
  ∃ A : Set ℕ, (∀ n ∈ A, 2 ≤ n) ∧ ∑' n : ℕ, rungSupportWeight J A n = 1 / 2

noncomputable def rungMisalign (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)

noncomputable def RungBad (J n : ℕ) : Prop :=
  ∀ M : ℕ, n ≤ M → M + 2 ≤ 2 * n → ¬ (rungMisalign J M ≤ 11 / 15)

noncomputable def rungRem (J : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n else rungRem J n

noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))

noncomputable def RungFatal (J n : ℕ) : Prop :=
  rungTail J n < rungRem J n ∧ rungRem J n < rungWeight J n

noncomputable def rungLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id

noncomputable def rungBadFinset (J : ℕ) : Finset ℕ :=
  (Finset.Icc 4 (rungLcm J / 2)).filter (fun n => RungBad J n)

noncomputable def rungDecisionHorizon (J : ℕ) : ℕ :=
  (insert 3 (rungBadFinset J)).max' ⟨3, Finset.mem_insert_self 3 _⟩

noncomputable def rungGreedySupport (J : ℕ) : Set ℕ := {n | rungWeight J n ≤ rungRem J n}

/-- States lem:tr-forced-greedy from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_unique_support_and_criterion in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_forced_greedy_unique_support_and_criterion {J : ℕ} (hJ : 2 ≤ J) :
    (∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 → A = rungGreedySupport J) ∧
      (HalfRung J ↔ ∀ n : ℕ, ¬ RungFatal J n) := by
  sorry

/-- States thm:tr-finite-decision from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rung_finite_decision in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rung_finite_decision {J : ℕ} (hJ : 2 ≤ J) :
    HalfRung J ↔ ∀ n : ℕ, 2 ≤ n → n ≤ rungDecisionHorizon J → ¬ RungFatal J n := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsJ
