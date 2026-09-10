/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import Solutions.PalomarCorpus.E257.Shared

open Set

namespace PalomarCorpus.E257.MixedWeightedCover
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)

noncomputable section

noncomputable def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)

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
    refine ⟨(toSource C), ?_, ?_⟩
    · simpa [PositiveCoverData.host_toSource] using hA
    · exact (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC
  · rintro ⟨C, hA, hC⟩
    refine ⟨ofSource C, ?_,
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC⟩
    simpa [PositiveCoverData.host] using hA

theorem MixedSupportClaim_eq :
    MixedSupportClaim ↔ ErdosProblems.Erdos257.PaperCompleteR7.MixedSupportClaim := by
  constructor
  · intro h E V hE0 hE hV A hA hInf b hb
    have hE' : FinitePrimeWeighted 2 E := by
      simpa [FinitePrimeWeighted_eq] using hE
    have hV' : HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mpr hV
    have := h E V hE0 hE' hV' A hA hInf b hb
    simpa [erdosSupportSeries_eq] using this
  · intro h E V hE0 hE hV A hA hInf b hb
    have hE' : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 E := by
      simpa [FinitePrimeWeighted_eq] using hE
    have hV' : ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mp hV
    have := h E V hE0 hE' hV' A hA hInf b hb
    simpa [erdosSupportSeries_eq] using this

theorem mixedSupportClaim : MixedSupportClaim :=
  MixedSupportClaim_eq.mpr ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim

end

end PalomarCorpus.E257.MixedWeightedCover
