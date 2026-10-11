import Solutions.PalomarCorpus.E257_01.DivisibilityWeightedSupport
import Solutions.PalomarCorpus.E257_01.PaperStructuresBO

open scoped BigOperators

/- Exact receiving declaration port. Runtime verification remains pending. -/
namespace Erdos257

def erdos_257.variants.primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

/-- The weighted cost of an exponent in base `b`. -/
noncomputable def erdos_257.variants.primeWeightedTerm
    (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (erdos_257.variants.primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ erdos_257.variants.primeSetPart P a - 1))

noncomputable def erdos_257.variants.finitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (erdos_257.variants.primeWeightedTerm b P))


theorem erdos_257.variants.finite_prime_weighted_support :
    (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
      erdos_257.variants.finitePrimeWeighted b A →
        Irrational (∑' a : ℕ,
          Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)) ∧
    (∀ H : Set ℕ, 0 ∉ H → erdos_257.variants.finitePrimeWeighted 2 H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b →
          Irrational (∑' a : ℕ,
            Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)) := by
  change PalomarCorpus.E257.DivisibilityWeightedSupport.DivisibilityWeightedClaim
  exact PalomarCorpus.E257.DivisibilityWeightedSupport.divisibilityWeightedClaim

namespace MixedSupport

open Finset
open scoped BigOperators

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- Positive-weight finite divisor frames covering the support. The weights sum
to one; fractional divisor-count majorants have a summable weighted budget. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

end MixedSupport

open MixedSupport

theorem erdos_257.variants.arbitrary_weight_mixed_support
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : erdos_257.variants.finitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) := by
  let D' : PalomarCorpus.E257.PaperStructuresBO.LogBudgetCover V :=
    ⟨D.frame, D.weight, D.exponent, D.coefficient, D.frame_positive,
     D.weight_positive, D.weight_sum, D.exponent_bounds, D.coefficient_nonneg,
     D.column_summable, D.covers, D.majorises, D.budget_summable⟩
  change PalomarCorpus.E257_01.Shared.FinitePrimeWeighted 2 E at hE
  change ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
    Irrational (PalomarCorpus.E257_01.Shared.erdosSupportSeries b A)
  exact PalomarCorpus.E257.PaperStructuresBO.arbitraryWeightMixedSupport_allBase_hereditary
    E V hE0 hE D'

end Erdos257

#print axioms Erdos257.erdos_257.variants.finite_prime_weighted_support
#print axioms Erdos257.erdos_257.variants.arbitrary_weight_mixed_support
