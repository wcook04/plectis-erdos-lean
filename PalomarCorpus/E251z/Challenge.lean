/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band z

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
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsZ
open Filter
open Topology
open Finset
open scoped BigOperators
/-- Event counts with classical membership made explicit in the definition. Local copy of ErdosProblems.Erdos251.PaperR7.eventStarts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.eventFrequency, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
/-- Asymptotic density zero, with no assumption of existence of a density. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.ZeroDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PerturbationGrowth.scale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ)
/-- The actual zero-based prime enumeration, not an arbitrary model. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
/-- Classical PNT input only for the ORIGINAL nth prime. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
/-- Schlage-Puchta, Lemma 4, in zero-based consecutive-prime-gap notation. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.SchlagePuchtaLemma4, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.cumulative, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulative (b : ℕ → ℕ) (n : ℕ) : ℕ := 2 + ∑ i ∈ range n, b i
/-- Local copy of ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
/-- States res:jointcountermodel from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
end PalomarCorpus.E251.PaperStatementsZ
