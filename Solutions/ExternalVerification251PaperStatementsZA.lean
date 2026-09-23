/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR21.PerturbedPrimePositions
import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.NonconcentrationCoreR11`,
`ErdosProblems.Erdos251.PaperCompleteR21.PerturbedPrimePositions`,
`ErdosProblems.Erdos251.PrimeGapDyadicTail`.
-/

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology

namespace Erdos249257.ExternalVerification251PaperStatementsZA

noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

theorem nonconcentration_does_not_force_irrationality
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (hPNT : Tendsto (fun n : ℕ => (prime0 n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1)) :
    ∃ (b : ℕ → ℕ) (q : ℚ),
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (q : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, (b n : ℤ) - primeGap0 n = 0 ∨ (b n : ℤ) - primeGap0 n = (M : ℤ)) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ n, b n % M = primeGap0 n % M) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ 2 + ∑ i ∈ range n, b i) ∧
      (∀ n, 2 + ∑ i ∈ range n, b i ≤ prime0 n + M * n) ∧
      Tendsto (fun n : ℕ => ((2 + ∑ i ∈ range n, b i : ℕ) : ℝ) / ((n : ℝ) * Real.log n))
        atTop (𝓝 1) := @ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality M hM K hSP hPNT

end Erdos249257.ExternalVerification251PaperStatementsZA
