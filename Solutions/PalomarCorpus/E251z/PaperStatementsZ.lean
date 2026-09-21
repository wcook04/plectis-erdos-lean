/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.ActualPrimePaperR11
import ErdosProblems.Erdos251.GrowingBlocksR11
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR21.JointPrimeGapCountermodel
import ErdosProblems.Erdos251.PaperSparseCouplingR7
import ErdosProblems.Erdos251.PerturbationGrowthR11
import ErdosProblems.Erdos251.PrimeSourceR11
import ErdosProblems.Erdos251.SparsePolylogR11
import Solutions.PalomarCorpus.E251z.Statement

open Filter
open Topology
open Finset
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsZ

theorem short_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ b : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n, n < K → b n = primeGap0 n) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ᶠ n : ℕ in atTop, ((b n - primeGap0 n : ℕ) : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        b n ≡ primeGap0 n [MOD q] ∧ cumulative b n ≡ prime0 n [MOD q]) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X => blockTV primeGap0 b X (m X)) atTop (𝓝 0)) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ cumulative b n) ∧
      (∀ᶠ n : ℕ in atTop, (cumulative b n : ℝ) - prime0 n
        ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1) := by
  apply ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel <;> assumption

end PalomarCorpus.E251.PaperStatementsZ
