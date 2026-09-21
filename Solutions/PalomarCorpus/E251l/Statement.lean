/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251l

Every non-theorem declaration of `PalomarCorpus/E251l/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsL
open scoped BigOperators
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- **(P)**: for every positive modulus and every cutoff, some pair of indices beyond the cutoff, congruent modulo the modulus, has a nonintegral tail difference. Local copy of ErdosProblems.Erdos251.CofinalFreePairNonintegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
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
end PalomarCorpus.E251.PaperStatementsL
