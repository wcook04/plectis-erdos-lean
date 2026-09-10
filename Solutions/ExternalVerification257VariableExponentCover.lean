/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.PaperCompleteR8.PositiveCoverReturn

/-!
# Source transport for variable-exponent fractional-cover irrationality

The compared statement is
`ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim`.
-/

namespace Erdos249257.ExternalVerification257VariableExponentCover

open Set

noncomputable section

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

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

def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)

theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

def toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises

def ofSource
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

end Erdos249257.ExternalVerification257VariableExponentCover
