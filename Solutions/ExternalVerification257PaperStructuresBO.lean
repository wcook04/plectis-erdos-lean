/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets
import ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightMixedClaim
import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets`,
`ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightMixedClaim`,
`ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBO

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

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `LogBudgetCover` and its source `ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover` carry the same
fields, so each converts into the other field by field. -/
def LogBudgetCover_transport_toSrc {A : Set ℕ} (x : LogBudgetCover A) :
    ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A :=
  ⟨x.frame, x.weight, x.exponent, x.coefficient, x.frame_positive, x.weight_positive, x.weight_sum, x.exponent_bounds, x.coefficient_nonneg, x.column_summable, x.covers, x.majorises, x.budget_summable⟩

/-- The inverse of `LogBudgetCover_transport_toSrc`. -/
def LogBudgetCover_transport_ofSrc {A : Set ℕ} (x : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
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

end Erdos249257.ExternalVerification257PaperStructuresBO
