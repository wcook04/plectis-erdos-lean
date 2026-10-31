/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperCompleteR20.CriticalMeanWhole
import ErdosProblems.Erdos1041.PaperCriticalConsequencesR10

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperAnalyticTargets`,
`ErdosProblems.Erdos1041.PaperCompleteR20.CriticalMeanWhole`,
`ErdosProblems.Erdos1041.PaperCriticalConsequencesR10`.
-/

open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
open Real

namespace Erdos249257.ExternalVerification1041PaperStatementsP

noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))

noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R

noncomputable def radialEqualityPolynomial (n : ℕ) (h lam : ℂ) : ℂ[X] := (X - C h) ^ n - C lam

theorem critical_value_three_budgets_sharp (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ) :
    let R := ‖lam‖ ^ (1 / (n : ℝ))
    let f := radialEqualityPolynomial n h lam
    f.Monic ∧ f.natDegree = n ∧ RootsInClosedDisc f h R ∧
    CriticalEnumeration f (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R := @ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets_sharp n hn h lam

end Erdos249257.ExternalVerification1041PaperStatementsP
