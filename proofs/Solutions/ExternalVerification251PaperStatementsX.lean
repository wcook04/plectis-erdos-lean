/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.ActualPrimePaperR11
import ErdosProblems.Erdos251.GrowingBlocksR11
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR21.JointPrimeGapCountermodel
import ErdosProblems.Erdos251.PaperSparseCouplingR7
import ErdosProblems.Erdos251.PerturbationGrowthR11
import ErdosProblems.Erdos251.PrimeSourceR11
import ErdosProblems.Erdos251.SparsePolylogR11

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.ActualPrimePaperR11`, `ErdosProblems.Erdos251.GrowingBlocksR11`,
`ErdosProblems.Erdos251.NonconcentrationCoreR11`,
`ErdosProblems.Erdos251.PaperCompleteR21.JointPrimeGapCountermodel`,
`ErdosProblems.Erdos251.PaperSparseCouplingR7`,
`ErdosProblems.Erdos251.PerturbationGrowthR11`, `ErdosProblems.Erdos251.PrimeSourceR11`,
`ErdosProblems.Erdos251.SparsePolylogR11`.
-/

open Filter
open Topology
open Finset
open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsX

noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)

noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)

noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))

noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}

noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ)

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}

noncomputable def cumulative (b : ℕ → ℕ) (n : ℕ) : ℕ := 2 + ∑ i ∈ range n, b i

noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α

theorem long_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ e : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      (∀ n, n < K → e n = 0) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
        cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
      FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ)) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X =>
          blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0)) ∧
      (∀ n, prime0 n ≤ cumulative (fun i => primeGap0 i + e i) n) ∧
      (∀ᶠ n : ℕ in atTop,
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
          ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n =>
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1) := by
  apply ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel <;> assumption

end Erdos249257.ExternalVerification251PaperStatementsX
