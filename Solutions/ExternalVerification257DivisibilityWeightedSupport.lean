/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

/-!
# Source transport for divisibility-weighted support irrationality

The compared statement is `ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim`.
The Claim Prop and its unfolding are re-declared in Mathlib vocabulary and identified with
the source chain so the transported statement is the source statement.
-/

namespace Erdos249257.ExternalVerification257DivisibilityWeightedSupport

open Set

noncomputable section

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))

theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

theorem primeSetPart_eq :
    primeSetPart = ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart := rfl

theorem primeWeightedTerm_eq :
    primeWeightedTerm = ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm := by
  funext b P a
  simp [primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm,
    primeSetPart_eq]

theorem FinitePrimeWeighted_eq :
    FinitePrimeWeighted = ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted := by
  funext b A
  simp [FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted,
    primeWeightedTerm_eq]

theorem DivisibilityWeightedClaim_eq :
    DivisibilityWeightedClaim =
      ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim := by
  unfold DivisibilityWeightedClaim
    ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim
  rw [FinitePrimeWeighted_eq, erdosSupportSeries_eq]

theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  rw [DivisibilityWeightedClaim_eq]
  exact ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim

end

end Erdos249257.ExternalVerification257DivisibilityWeightedSupport
