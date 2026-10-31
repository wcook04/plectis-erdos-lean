/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.PositiveCoverReturn
import Solutions.PalomarCorpus.E257_01.Statement

open Set

namespace PalomarCorpus.E257.VariableExponentCover
export PalomarCorpus.E257_01.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)

noncomputable section

theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

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

theorem PositiveCoverData.host_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (ofSource C).host = C.host := rfl

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem StrengthenedPositiveCoverClaim_iff :
    StrengthenedPositiveCoverClaim ↔
      ErdosProblems.Erdos257.PaperCompleteR7.StrengthenedPositiveCoverClaim := by
  constructor
  · intro h C hC A hA hInf b hb
    have hC' : (ofSource C).StrengthenedCostSummable :=
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC
    have hA' : A ⊆ (ofSource C).host := by
      simpa [PositiveCoverData.host_ofSource] using hA
    have := h (ofSource C) hC' A hA' hInf b hb
    simpa [erdosSupportSeries_eq] using this
  · intro h C hC A hA hInf b hb
    have hC' : (toSource C).StrengthenedCostSummable :=
      (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC
    have hA' : A ⊆ (toSource C).host := by
      simpa [PositiveCoverData.host_toSource] using hA
    have := h (toSource C) hC' A hA' hInf b hb
    simpa [erdosSupportSeries_eq] using this

theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim :=
  StrengthenedPositiveCoverClaim_iff.mpr
    ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim

end

end PalomarCorpus.E257.VariableExponentCover
