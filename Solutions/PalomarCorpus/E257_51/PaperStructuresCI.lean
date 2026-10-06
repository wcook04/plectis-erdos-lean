/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.PaperCompleteR8.OldCoverObstruction
import ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost
import Solutions.PalomarCorpus.E257_51.Statement

open Finset
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCI
export PalomarCorpus.E257_51.Shared (erdosSupportSeries primeSetPart primeWeightedTerm)

/-- The copied structure `PositiveCoverData` and its source `ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData` carry the same
fields, so each converts into the other field by field. -/
noncomputable def PositiveCoverData_transport_toSrc (x : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData :=
  ⟨x.frame, x.exponent, x.coefficient, x.frame_positive, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.majorises⟩

/-- The inverse of `PositiveCoverData_transport_toSrc`. -/
noncomputable def PositiveCoverData_transport_ofSrc (x : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    PositiveCoverData :=
  ⟨x.frame, x.exponent, x.coefficient, x.frame_positive, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.majorises⟩

@[simp] theorem PositiveCoverData_transport_toSrc_frame
    (x : PositiveCoverData) :
    (PositiveCoverData_transport_toSrc x).frame = x.frame := rfl

@[simp] theorem PositiveCoverData_transport_ofSrc_frame
    (x : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData_transport_ofSrc x).frame = x.frame := rfl

@[simp] theorem PositiveCoverData_transport_toSrc_exponent
    (x : PositiveCoverData) :
    (PositiveCoverData_transport_toSrc x).exponent = x.exponent := rfl

@[simp] theorem PositiveCoverData_transport_ofSrc_exponent
    (x : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData_transport_ofSrc x).exponent = x.exponent := rfl

@[simp] theorem PositiveCoverData_transport_toSrc_coefficient
    (x : PositiveCoverData) :
    (PositiveCoverData_transport_toSrc x).coefficient = x.coefficient := rfl

@[simp] theorem PositiveCoverData_transport_ofSrc_coefficient
    (x : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData_transport_ofSrc x).coefficient = x.coefficient := rfl

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover` is the same function. -/
theorem HasStrengthenedPositiveCover_transport_def : @HasStrengthenedPositiveCover = @ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover := by
  first
  | (rfl; done)
  | (simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HasStrengthenedPositiveCover ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover; done)
  | (unfold HasStrengthenedPositiveCover ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover <;> simp only [ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (ext x; simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a; fun_induction HasStrengthenedPositiveCover a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a; induction a <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a; induction a <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a; induction a <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a; simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a b; fun_induction HasStrengthenedPositiveCover a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; induction b <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b; simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (funext a b c; fun_induction HasStrengthenedPositiveCover a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction c <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover, *]; done)
  | (funext a b c; simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (simp [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [HasStrengthenedPositiveCover, ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover] <;> rfl; done)
  | (funext v1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; apply propext; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold HasStrengthenedPositiveCover ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold HasStrengthenedPositiveCover ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover; congr 1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover` is the same function. -/
theorem HasOldPositiveCover_transport_def : @HasOldPositiveCover = @ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover := by
  first
  | (rfl; done)
  | (simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HasOldPositiveCover ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover; done)
  | (unfold HasOldPositiveCover ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (ext x; simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a; fun_induction HasOldPositiveCover a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a; induction a <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a; simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a b; fun_induction HasOldPositiveCover a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b; simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (funext a b c; fun_induction HasOldPositiveCover a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def, *]; done)
  | (funext a b c; simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (simp [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [HasOldPositiveCover, ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover, HasStrengthenedPositiveCover_transport_def] <;> rfl; done)
  | (funext v1; unfold HasOldPositiveCover ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover <;> simp only [HasStrengthenedPositiveCover_transport_def] <;> rfl; done)
  | (funext v1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; apply propext; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold HasOldPositiveCover ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold HasOldPositiveCover ErdosProblems.Erdos257.PaperCompleteR8.HasOldPositiveCover; congr 1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨PositiveCoverData_transport_ofSrc w, hw⟩); done)

theorem exists_strengthened_not_old_or_weighted_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A ∧
      (¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  simp only [HasStrengthenedPositiveCover_transport_def, HasOldPositiveCover_transport_def]
  exact @ErdosProblems.Erdos257.PaperCompleteR8.exists_strengthened_not_old_or_weighted_host

end PalomarCorpus.E257.PaperStructuresCI
