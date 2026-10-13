/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightMixedClaim
import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget
import Solutions.PalomarCorpus.E257_01.Statement

open Finset
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBO
export PalomarCorpus.E257_01.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)

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

theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) := @ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary E V hE0 hE (LogBudgetCover_transport_toSrc D)

end PalomarCorpus.E257.PaperStructuresBO
