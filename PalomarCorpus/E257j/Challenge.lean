/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band j

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open Classical

namespace PalomarCorpus.E257.PaperStatementsJ
open Filter
open Topology
open Classical
/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)
/-- The mass that the support `A` puts at rank `n`: this is `Set.indicator A (rungWeight J)`, so `∑' n, rungSupportWeight J A n` is the manuscript's `∑_{n ∈ A} w_n^{(J)}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungSupportWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungSupportWeight (J : ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A then rungWeight J n else 0
/-- The manuscript's `HalfRung(J)`: some `A ⊆ {2,3,…}` has `∑_{n ∈ A} w_n^{(J)} = 1/2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.HalfRung, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfRung (J : ℕ) : Prop :=
  ∃ A : Set ℕ, (∀ n ∈ A, 2 ≤ n) ∧ ∑' n : ℕ, rungSupportWeight J A n = 1 / 2
/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungMisalign, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungMisalign (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
/-- A rank `n` is **bad** for `J` when no `M ∈ [n, 2n-2]` passes the witness test `μ_J(M) ≤ 11/15`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.RungBad, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RungBad (J n : ℕ) : Prop :=
  ∀ M : ℕ, n ≤ M → M + 2 ≤ 2 * n → ¬ (rungMisalign J M ≤ 11 / 15)
/-- The greedy residual just before rank `n` is examined; `rungRem J 0 = 1/2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungRem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungRem (J : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n else rungRem J n
/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
/-- Rank `n` is **fatal** when the residual sits strictly inside the gap `(T_{n+1}^{(J)}, w_n^{(J)})`, which no later tail can repair. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.RungFatal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RungFatal (J n : ℕ) : Prop :=
  rungTail J n < rungRem J n ∧ rungRem J n < rungWeight J n
/-- The manuscript's `L_J = lcm(2,3,…,J)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id
/-- The bad ranks inside the manuscript's finite window `[4, L_J/2]`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungBadFinset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungBadFinset (J : ℕ) : Finset ℕ :=
  (Finset.Icc 4 (rungLcm J / 2)).filter (fun n => RungBad J n)
/-- The manuscript's `B(J) = max(bad ∪ {3})`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungDecisionHorizon, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungDecisionHorizon (J : ℕ) : ℕ :=
  (insert 3 (rungBadFinset J)).max' ⟨3, Finset.mem_insert_self 3 _⟩
/-- The greedy support: the ranks the greedy rule takes. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungGreedySupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungGreedySupport (J : ℕ) : Set ℕ := {n | rungWeight J n ≤ rungRem J n}
/-- States lem:tr-forced-greedy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_unique_support_and_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_forced_greedy_unique_support_and_criterion {J : ℕ} (hJ : 2 ≤ J) :
    (∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 → A = rungGreedySupport J) ∧
      (HalfRung J ↔ ∀ n : ℕ, ¬ RungFatal J n) := by
  sorry
/-- States thm:tr-finite-decision from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rung_finite_decision in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rung_finite_decision {J : ℕ} (hJ : 2 ≤ J) :
    HalfRung J ↔ ∀ n : ℕ, 2 ≤ n → n ≤ rungDecisionHorizon J → ¬ RungFatal J n := by
  sorry
end PalomarCorpus.E257.PaperStatementsJ
