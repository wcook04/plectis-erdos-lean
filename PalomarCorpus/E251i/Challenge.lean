/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band i

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open Finset

namespace PalomarCorpus.E251.PaperStatementsI
open Filter
open Topology
open Finset
/-- A level-k step. The square is convenient; sharp constants are not claimed. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.gap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gap (k : ℕ) : ℕ := (k + 4) ^ 2
/-- A level-k capacity, allowing two successive modulus upgrades. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.amplitude, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k
/-- A stage is allowed only after its entire future budget is available. The additional linear bound ensures geometric summability independently of how rapidly the supplied envelope grows. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.Ready, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1
/-- Reciprocal-integer characterisation of upper Banach density zero. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.UpperBanachZero, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L
/-- Upgrade by one level exactly when the future budget allows it. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.upgrade, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k
/-- State = (centre, level), with no assumed rate for the envelope. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.state, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)
/-- Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.centre, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1
/-- States long251:res:local-targets from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem local_target_interval (a : ℕ → ℕ) {A η : ℝ}
    (ha : HasSum (fun n => (a n : ℝ)/2^(n+1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) (hη : 0 < η) :
    ∃ start : ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      A < l ∧ l < u ∧ u < A+η ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre f start)) ∧
        (∀ n < K, a n+e n = a n) ∧
        (∀ᶠ n in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n+e n : ℕ) : ℝ)/2^(n+1)) r := by
  sorry
end PalomarCorpus.E251.PaperStatementsI
