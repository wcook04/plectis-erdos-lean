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
open Finset
open scoped Topology
open scoped BigOperators
open Topology

namespace PalomarCorpus.E251.PaperStatementsZA
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology
/-- Asymptotic density zero, with no assumption of existence of a density. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.ZeroDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- States long251:res:nonconc-primes from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
        atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsZA
