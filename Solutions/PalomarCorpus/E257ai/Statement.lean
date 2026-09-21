/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ai

Every non-theorem declaration of `PalomarCorpus/E257ai/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Classical

namespace PalomarCorpus.E257.PaperStatementsAI
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
end PalomarCorpus.E257.PaperStatementsAI
