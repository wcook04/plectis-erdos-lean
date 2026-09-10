/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

/-!
# Source transport for mixed weighted-cover synchronisation

The compared statement is `ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim`.
-/

namespace Erdos249257.ExternalVerification257MixedWeightedCover

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

def MixedSupportClaim : Prop :=
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

end Erdos249257.ExternalVerification257MixedWeightedCover
