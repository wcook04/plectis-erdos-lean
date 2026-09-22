/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251i

Every non-theorem declaration of `PalomarCorpus/E251i/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E251.PaperStatementsI
