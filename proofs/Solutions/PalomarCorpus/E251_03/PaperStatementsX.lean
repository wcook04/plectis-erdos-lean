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
import Solutions.PalomarCorpus.E251_03.Statement

open Filter
open Topology
open Finset
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsX
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)

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

end PalomarCorpus.E251.PaperStatementsX
