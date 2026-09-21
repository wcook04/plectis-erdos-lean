/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band p

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
open Real

namespace PalomarCorpus.E1041.PaperStatementsP
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
open Real
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalEnumeration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootsInClosedDisc, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- Local copy of ErdosProblems.Erdos1041.radialEqualityPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def radialEqualityPolynomial (n : ℕ) (h lam : ℂ) : ℂ[X] := (X - C h) ^ n - C lam
/-- States eq:critical-value-power-budget, eq:critical-value-quadratic-budget, res:critical-value-budget from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets_sharp in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem critical_value_three_budgets_sharp (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ) :
    let R := ‖lam‖ ^ (1 / (n : ℝ))
    let f := radialEqualityPolynomial n h lam
    f.Monic ∧ f.natDegree = n ∧ RootsInClosedDisc f h R ∧
    CriticalEnumeration f (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R := by
  sorry
end PalomarCorpus.E1041.PaperStatementsP
