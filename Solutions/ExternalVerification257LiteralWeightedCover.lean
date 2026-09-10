/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticSeparationReturn

/-!
# Source transport for literal weighted-cover separation

The compared statements are
`ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_not_strengthened_host`
and
`ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_obstruction_with_mixed_heredity`.
-/

namespace Erdos249257.ExternalVerification257LiteralWeightedCover

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

structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d

def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)

def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}

def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))

def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable

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

def PositiveCoverData.toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises

def PositiveCoverData.ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises

theorem PositiveCoverData.host_toSource (C : PositiveCoverData) :
    C.host = C.toSource.host := rfl

theorem PositiveCoverData.cost_toSource (C : PositiveCoverData) :
    C.cost = C.toSource.cost := rfl

theorem PositiveCoverData.exponent_toSource (C : PositiveCoverData) :
    C.exponent = C.toSource.exponent := rfl

theorem PositiveCoverData.StrengthenedCostSummable_toSource (C : PositiveCoverData) :
    C.StrengthenedCostSummable ↔ C.toSource.StrengthenedCostSummable := by
  unfold PositiveCoverData.StrengthenedCostSummable
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.StrengthenedCostSummable
  rw [PositiveCoverData.cost_toSource, PositiveCoverData.exponent_toSource]

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData.ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem HasStrengthenedPositiveCover_iff (A : Set ℕ) :
    HasStrengthenedPositiveCover A ↔
      ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover A := by
  constructor
  · rintro ⟨C, hA, hC⟩
    refine ⟨C.toSource, ?_, (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC⟩
    simpa [PositiveCoverData.host_toSource] using hA
  · rintro ⟨C, hA, hC⟩
    refine ⟨PositiveCoverData.ofSource C, ?_,
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC⟩
    simpa [PositiveCoverData.host] using hA

def LogBudgetCover.toSource {A : Set ℕ} (C : LogBudgetCover A) :
    ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A where
  frame := C.frame
  weight := C.weight
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := C.weight_positive
  weight_sum := C.weight_sum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := C.covers
  majorises := C.majorises
  budget_summable := C.budget_summable

def LogBudgetCover.ofSource {A : Set ℕ}
    (C : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    LogBudgetCover A where
  frame := C.frame
  weight := C.weight
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := C.weight_positive
  weight_sum := C.weight_sum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := C.covers
  majorises := C.majorises
  budget_summable := C.budget_summable

theorem isEmpty_logBudgetCover_iff (A : Set ℕ) :
    IsEmpty (LogBudgetCover A) ↔
      IsEmpty (ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) := by
  constructor
  · intro h
    exact ⟨fun C => (h.elim (LogBudgetCover.ofSource C))⟩
  · intro h
    exact ⟨fun C => (h.elim (C.toSource))⟩

theorem exists_weighted_not_strengthened_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      ¬ HasStrengthenedPositiveCover A ∧ IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hrec, hncover, hn, hirr⟩ :=
    ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_not_strengthened_host
  refine ⟨A, hinf, hzero, ?_, hrec, ?_, ?_, ?_⟩
  · simpa [FinitePrimeWeighted_eq] using hw
  · intro hA
    exact hncover ((HasStrengthenedPositiveCover_iff A).mp hA)
  · exact (isEmpty_logBudgetCover_iff A).mpr hn
  · intro B hBA hBinf b hb
    simpa [erdosSupportSeries_eq] using hirr B hBA hBinf b hb

theorem exists_weighted_obstruction_with_mixed_heredity :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ V : Set ℕ, HasStrengthenedPositiveCover V →
        ∀ B : Set ℕ, B ⊆ A ∪ V → B.Infinite → ∀ b : ℕ, 2 ≤ b →
          Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hn, hmix⟩ :=
    ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_obstruction_with_mixed_heredity
  refine ⟨A, hinf, hzero, ?_, (isEmpty_logBudgetCover_iff A).mpr hn, ?_⟩
  · simpa [FinitePrimeWeighted_eq] using hw
  · intro V hV B hB hBi b hb
    have hV' : ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mp hV
    simpa [erdosSupportSeries_eq] using hmix V hV' B hB hBi b hb

end

end Erdos249257.ExternalVerification257LiteralWeightedCover
