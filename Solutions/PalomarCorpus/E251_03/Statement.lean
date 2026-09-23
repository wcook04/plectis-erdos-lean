/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251_03

Every non-theorem declaration of `PalomarCorpus/E251_03/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Finset
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E251_03.Shared
/-- A set of natural numbers has density zero when for every positive real `ε` all sufficiently large `N` have fewer than `ε * N` elements below `N`. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR7.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
end PalomarCorpus.E251_03.Shared

namespace PalomarCorpus.E251.PaperStatementsR
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (prime0 primeGap0)
/-- Four distinct primes with two outer gaps differing by r. Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.quadCandidates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z =>
      0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))
/-- Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.shiftedMatches, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)
end PalomarCorpus.E251.PaperStatementsR

namespace PalomarCorpus.E251.PaperStatementsF
open scoped BigOperators
open Finset
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity)
end PalomarCorpus.E251.PaperStatementsF

namespace PalomarCorpus.E251.PaperStatementsZA
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
end PalomarCorpus.E251.PaperStatementsZA

namespace PalomarCorpus.E251.PaperStatementsK
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity)
end PalomarCorpus.E251.PaperStatementsK

namespace PalomarCorpus.E251.PaperStatementsX
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
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
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PerturbationGrowth.scale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ)
/-- Classical PNT input only for the ORIGINAL nth prime. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
/-- Schlage-Puchta, Lemma 4, in zero-based consecutive-prime-gap notation. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.SchlagePuchtaLemma4, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.cumulative, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulative (b : ℕ → ℕ) (n : ℕ) : ℕ := 2 + ∑ i ∈ range n, b i
/-- Local copy of ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
end PalomarCorpus.E251.PaperStatementsX

namespace PalomarCorpus.E251.PaperStatementsY
open scoped BigOperators
open Filter
open Topology
open Finset
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.shift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shift (T : ℕ → ℝ) (h N : ℕ) : ℝ := T (N + h) - T N
/-- The real term in the corresponding consecutive-prime-gap series. Local copy of ErdosProblems.Erdos251.primeGapDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- Finite dyadic partial sum of the actual consecutive prime gaps. Local copy of ErdosProblems.Erdos251.primeGapPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- The genuine scaled tail after the first `N+1` prime-gap terms. Local copy of ErdosProblems.Erdos251.realPrimeGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))
end PalomarCorpus.E251.PaperStatementsY

namespace PalomarCorpus.E251.PaperStatementsA
open Filter
open Topology
open Finset
end PalomarCorpus.E251.PaperStatementsA

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- The coefficient emitted by an unrestricted integer carry. Local copy of ErdosProblems.Erdos251.carryCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)
/-- The finite dyadic series emitted by `carryCoeff`. Local copy of ErdosProblems.Erdos251.carryPartialSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)
/-- A positive even polynomial gap word. It is not the actual prime-gap word; it is an exact stress test for attempts using only coarse gap properties. Local copy of ErdosProblems.Erdos251.polynomialGapWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)
/-- The rational polynomial tail orbit paired with `polynomialGapWord`. Local copy of ErdosProblems.Erdos251.polynomialTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251.PaperStatementsG
