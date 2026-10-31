/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for divisibility-weighted support irrationality

A finite prime-weighted cost on an infinite support with no zero forces
irrationality of the reciprocal-Mersenne series at that base, and a finite
binary weighted cost on a host forces all-base hereditary irrationality of
every infinite subset. This is the long-record weighted claim. It does not
assert irrationality for every infinite support, and Erdős #257 remains open.
-/

namespace Erdos249257.ExternalVerification257DivisibilityWeightedSupport

open Set

noncomputable section

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- The full prime-power part determined by a finite set of primes. -/
def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

/-- The literal weighted term at an integer base. -/
def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

/-- The weighted hypothesis, not its irrationality conclusion. -/
def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

/-- Open Lean goal for long thm:257-weighted, including the all-base
hereditary consequence of a finite binary weighted mass. -/
def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))

theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  sorry

end

end Erdos249257.ExternalVerification257DivisibilityWeightedSupport
