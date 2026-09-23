/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.CoverIndependentPeriodicMean
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleAssembly
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBound
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBoundPaperForm
import ErdosProblems.Erdos257.PaperCompleteR21.FiniteFamilyCoverCost
import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval
import ErdosProblems.Erdos257.PaperCompleteR8.FiniteMeans
import ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence
import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget
import Solutions.PalomarCorpus.E257_38.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBS
export PalomarCorpus.E257_38.Shared (condExceedProb divisorMajorantCost exceedInd frameLcm framePotential incidenceCount kappaOne kernelWeight logMajorantCosts progressionMean)

/-- The copied structure `LogBudgetCover` and its source `ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover` carry the same
fields, so each converts into the other field by field. -/
noncomputable def LogBudgetCover_transport_toSrc {A : Set ℕ} (x : LogBudgetCover A) :
    ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A :=
  ⟨x.frame, x.weight, x.exponent, x.coefficient, x.frame_positive, x.weight_positive, x.weight_sum, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.covers, x.majorises, x.budget_summable⟩

/-- The inverse of `LogBudgetCover_transport_toSrc`. -/
noncomputable def LogBudgetCover_transport_ofSrc {A : Set ℕ} (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    LogBudgetCover A :=
  ⟨x.frame, x.weight, x.exponent, x.coefficient, x.frame_positive, x.weight_positive, x.weight_sum, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.covers, x.majorises, x.budget_summable⟩

@[simp] theorem LogBudgetCover_transport_toSrc_frame {A : Set ℕ}
    (x : LogBudgetCover A) :
    (LogBudgetCover_transport_toSrc x).frame = x.frame := rfl

@[simp] theorem LogBudgetCover_transport_ofSrc_frame {A : Set ℕ}
    (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    (LogBudgetCover_transport_ofSrc x).frame = x.frame := rfl

@[simp] theorem LogBudgetCover_transport_toSrc_weight {A : Set ℕ}
    (x : LogBudgetCover A) :
    (LogBudgetCover_transport_toSrc x).weight = x.weight := rfl

@[simp] theorem LogBudgetCover_transport_ofSrc_weight {A : Set ℕ}
    (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    (LogBudgetCover_transport_ofSrc x).weight = x.weight := rfl

@[simp] theorem LogBudgetCover_transport_toSrc_exponent {A : Set ℕ}
    (x : LogBudgetCover A) :
    (LogBudgetCover_transport_toSrc x).exponent = x.exponent := rfl

@[simp] theorem LogBudgetCover_transport_ofSrc_exponent {A : Set ℕ}
    (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    (LogBudgetCover_transport_ofSrc x).exponent = x.exponent := rfl

@[simp] theorem LogBudgetCover_transport_toSrc_coefficient {A : Set ℕ}
    (x : LogBudgetCover A) :
    (LogBudgetCover_transport_toSrc x).coefficient = x.coefficient := rfl

@[simp] theorem LogBudgetCover_transport_ofSrc_coefficient {A : Set ℕ}
    (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    (LogBudgetCover_transport_ofSrc x).coefficient = x.coefficient := rfl

set_option maxRecDepth 8000 in
@[simp] theorem LogBudgetCover_cost_transport_def {A : Set ℕ} (C : LogBudgetCover A) :
    ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost (LogBudgetCover_transport_toSrc C) = LogBudgetCover.cost C := by
  first
  | (rfl; done)
  | (simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (with_unfolding_all rfl; done)
  | (unfold LogBudgetCover.cost ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost; done)
  | (unfold LogBudgetCover.cost ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (ext x; simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a; fun_induction LogBudgetCover.cost a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a; induction a <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a; induction a <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a; induction a <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a; simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a b; fun_induction LogBudgetCover.cost a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; induction b <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; induction a generalizing b <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; induction b generalizing a <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b; simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (funext a b c; fun_induction LogBudgetCover.cost a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction c <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost, *]; done)
  | (funext a b c; simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)
  | (simp [LogBudgetCover.cost, ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover.cost]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts` is the same function. -/
theorem admissibleLogCoverCosts_transport_def : @admissibleLogCoverCosts = @ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts := by
  first
  | (rfl; done)
  | (simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold admissibleLogCoverCosts ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts; done)
  | (unfold admissibleLogCoverCosts ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (ext x; simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a; fun_induction admissibleLogCoverCosts a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a; induction a <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a; induction a <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a; induction a <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a; simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a b; fun_induction admissibleLogCoverCosts a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b; simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (funext a b c; fun_induction admissibleLogCoverCosts a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def, *]; done)
  | (funext a b c; simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (simp [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [admissibleLogCoverCosts, ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts, LogBudgetCover_cost_transport_def] <;> rfl; done)
  | (funext v1; unfold admissibleLogCoverCosts ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts <;> simp only [LogBudgetCover_cost_transport_def] <;> rfl; done)
  | (funext v1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_ofSrc w, hw⟩); done)
  | (funext v1; apply propext; constructor; (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold admissibleLogCoverCosts ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_ofSrc w, hw⟩); done)
  | (funext v1; unfold admissibleLogCoverCosts ErdosProblems.Erdos257.PaperCompleteR8.admissibleLogCoverCosts; congr 1; ext x; constructor; (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_toSrc w, hw⟩); (rintro ⟨w, hw⟩; exact ⟨LogBudgetCover_transport_ofSrc w, hw⟩); done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost` is the same function. -/
theorem paperCoverCost_transport_def : @paperCoverCost = @ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost := by
  first
  | (rfl; done)
  | (simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold paperCoverCost ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost; done)
  | (unfold paperCoverCost ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (ext x; simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a; fun_induction paperCoverCost a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a; induction a <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a; induction a <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a; induction a <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a; simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a b; fun_induction paperCoverCost a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b; simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (funext a b c; fun_induction paperCoverCost a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, *]; done)
  | (funext a b c; simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (simp [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [paperCoverCost, ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost, LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def] <;> rfl; done)
  | (funext v1; unfold paperCoverCost ErdosProblems.Erdos257.PaperCompleteR21.paperCoverCost <;> simp only [LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def] <;> rfl; done)

theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) := by
  simp only [LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, paperCoverCost_transport_def]
  exact @ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge H hH

theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1 := by
  simp only [LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, paperCoverCost_transport_def]
  exact @ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_paperCoverCost_kappaOne_constant

theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ) := by
  simp only [LogBudgetCover_cost_transport_def, admissibleLogCoverCosts_transport_def, paperCoverCost_transport_def]
  exact @ErdosProblems.Erdos257.PaperCompleteR21.sup_condExceedProb_le_paperCoverCost F hF hne

end PalomarCorpus.E257.PaperStructuresBS
