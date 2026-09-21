/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.GrowingBlocksR11`,
`ErdosProblems.Erdos251.LogarithmicCarryAsymptoticsR8`,
`ErdosProblems.Erdos251.PaperCompleteR20.SparseConstructionAudit`.
-/

open Filter
open Topology
open Finset

namespace Erdos249257.ExternalVerification251PaperStatementsA

noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X

/-- States long251:res:sparse-rationalisation from the long record for Erdős problem #251.
Transported from ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X := by
  sorry

/-- States long251:res:polignacfail from the long record for Erdős problem #251. Transported
from
ErdosProblems.Erdos251.PaperR8.LogCarry.exists_logarithmic_recurring_values_countermodel in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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

end Erdos249257.ExternalVerification251PaperStatementsA
