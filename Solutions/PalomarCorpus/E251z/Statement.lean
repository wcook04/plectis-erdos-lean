/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251z

Every non-theorem declaration of `PalomarCorpus/E251z/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E251.PaperStatementsZ
