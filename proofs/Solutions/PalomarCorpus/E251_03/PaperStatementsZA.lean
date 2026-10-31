/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.PaperCompleteR21.PerturbedPrimePositions
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251_03.Statement

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsZA
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)

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

end PalomarCorpus.E251.PaperStatementsZA
