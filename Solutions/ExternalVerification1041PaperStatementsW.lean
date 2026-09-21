/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperReflectedCompletion

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperAnalyticTargets`,
`ErdosProblems.Erdos1041.PaperReflectedCompletion`.
-/

open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology

namespace Erdos249257.ExternalVerification1041PaperStatementsW

noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))

noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R

noncomputable def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖

theorem reflected_critical_value : ReflectedCriticalValue := @ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value

end Erdos249257.ExternalVerification1041PaperStatementsW
