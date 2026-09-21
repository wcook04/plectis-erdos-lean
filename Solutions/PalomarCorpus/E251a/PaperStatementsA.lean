/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.GrowingBlocksR11
import ErdosProblems.Erdos251.LogarithmicCarryAsymptoticsR8
import ErdosProblems.Erdos251.PaperCompleteR20.SparseConstructionAudit
import Solutions.PalomarCorpus.E251a.Statement

open Filter
open Topology
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsA

theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X := by
  apply ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling <;> assumption

theorem exists_logarithmic_recurring_values_countermodel :
    ∃ a U : ℕ → ℤ,
      let P : ℕ → ℤ := fun n => 3 + ∑ j ∈ range n, a (j + 1);
      (∀ n, 1 ≤ n → 0 < a n ∧ (2 : ℤ) ∣ a n) ∧
      (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ a i = 2 ∧ a j = 4) ∧
      (∀ B : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B < a n) ∧
      (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → a (n + h) = a n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (a n : ℝ) ≤ C * Real.log (n : ℝ)) ∧
      HasSum (fun j : ℕ => (a (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
      (∀ N, HasSum (fun j : ℕ => (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) (U N : ℝ)) ∧
      (∀ N h, ∃ z : ℤ,
        (∑' j : ℕ, (a (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
        (∑' j : ℕ, (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
      StrictMono P ∧ (∀ n, ∃ z : ℤ, P n = 2 * z + 1) ∧
      Tendsto (fun n : ℕ => (P n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := @ErdosProblems.Erdos251.PaperR8.LogCarry.exists_logarithmic_recurring_values_countermodel

end PalomarCorpus.E251.PaperStatementsA
