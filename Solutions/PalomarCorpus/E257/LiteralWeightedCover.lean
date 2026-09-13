/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticSeparationReturn
import Solutions.PalomarCorpus.E257.Statement

open Set

namespace PalomarCorpus.E257.LiteralWeightedCover
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)

noncomputable section

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

noncomputable def toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises

noncomputable def ofSource
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
    C.host = (toSource C).host := rfl

theorem PositiveCoverData.cost_toSource (C : PositiveCoverData) :
    C.cost = (toSource C).cost := rfl

theorem PositiveCoverData.exponent_toSource (C : PositiveCoverData) :
    C.exponent = (toSource C).exponent := rfl

theorem PositiveCoverData.StrengthenedCostSummable_toSource (C : PositiveCoverData) :
    C.StrengthenedCostSummable ↔ (toSource C).StrengthenedCostSummable := by
  unfold PositiveCoverData.StrengthenedCostSummable
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.StrengthenedCostSummable
  rw [PositiveCoverData.cost_toSource, PositiveCoverData.exponent_toSource]

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem HasStrengthenedPositiveCover_iff (A : Set ℕ) :
    HasStrengthenedPositiveCover A ↔
      ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover A := by
  constructor
  · rintro ⟨C, hA, hC⟩
    refine ⟨(toSource C), ?_, (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC⟩
    simpa [PositiveCoverData.host_toSource] using hA
  · rintro ⟨C, hA, hC⟩
    refine ⟨ofSource C, ?_,
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC⟩
    simpa [PositiveCoverData.host] using hA

noncomputable def LogBudgetCover.toSource {A : Set ℕ} (C : LogBudgetCover A) :
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

noncomputable def LogBudgetCover.ofSource {A : Set ℕ}
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

end PalomarCorpus.E257.LiteralWeightedCover
