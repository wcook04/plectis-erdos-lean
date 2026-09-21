/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band a

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

namespace PalomarCorpus.E251.PaperStatementsA
open Filter
open Topology
open Finset
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.testMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X
/-- States long251:res:sparse-rationalisation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X := by
  sorry
/-- States long251:res:polignacfail from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR8.LogCarry.exists_logarithmic_recurring_values_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
      Tendsto (fun n : ℕ => (P n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsA
