/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251g

Every non-theorem declaration of `PalomarCorpus/E251g/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- Cofinal failure of integral shifts for every fixed positive length. Local copy of ErdosProblems.Erdos251.CofinalNonintegralTailShifts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- The coefficient emitted by an unrestricted integer carry. Local copy of ErdosProblems.Erdos251.carryCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)
/-- The finite dyadic series emitted by `carryCoeff`. Local copy of ErdosProblems.Erdos251.carryPartialSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)
/-- Finite dyadic partial sum of the forward differences of a sequence. Local copy of ErdosProblems.Erdos251.dyadicDifferencePartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)
/-- Finite zero-based dyadic partial sum of a rational sequence. Local copy of ErdosProblems.Erdos251.dyadicPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)
/-- A positive even polynomial gap word. It is not the actual prime-gap word; it is an exact stress test for attempts using only coarse gap properties. Local copy of ErdosProblems.Erdos251.polynomialGapWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)
/-- The rational polynomial tail orbit paired with `polynomialGapWord`. Local copy of ErdosProblems.Erdos251.polynomialTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The term with denominator `2^n` used by the displayed formal conjecture. Local copy of ErdosProblems.Erdos251.primeDisplayedDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
/-- The real term in the normalized zero-based prime series. Local copy of ErdosProblems.Erdos251.primeDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
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
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251.PaperStatementsG
