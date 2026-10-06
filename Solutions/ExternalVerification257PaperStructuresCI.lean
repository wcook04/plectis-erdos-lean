/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.PaperCompleteR8.OldCoverObstruction
import ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets`,
`ErdosProblems.Erdos257.PaperCompleteR8.OldCoverObstruction`,
`ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresCI

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
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

noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable

noncomputable def HasOldPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.OldCostSummable

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `PositiveCoverData` and its source `ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData` carry the same
fields, so each converts into the other field by field. -/
def PositiveCoverData_transport_toSrc (x : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData :=
  ⟨x.frame, x.exponent, x.coefficient, x.frame_positive, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.majorises⟩

/-- The inverse of `PositiveCoverData_transport_toSrc`. -/
def PositiveCoverData_transport_ofSrc (x : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
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

end Erdos249257.ExternalVerification257PaperStructuresCI
