/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.PaperBoundedCarryR7

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperBoundedCarryR7`.
-/

open Filter
open Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsE

noncomputable def IsFactorialSpike (n : ℕ) : Prop := ∃ k : ℕ, 3 ≤ k ∧ n = k.factorial

noncomputable def factorialCarry (n : ℕ) : ℤ := by
  classical
  exact if IsFactorialSpike n then 6 else 4

noncomputable def factorialCarryDigit (n : ℕ) : ℤ :=
  if n = 0 then 0 else 2 * factorialCarry (n - 1) - factorialCarry n

theorem bounded_recurring_values_countermodel :
    (∀ n, 1 ≤ n → factorialCarryDigit n = 2 ∨
      factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8) ∧
    (∀ k, 3 ≤ k → factorialCarryDigit k.factorial = 2 ∧
      factorialCarryDigit (2 * k.factorial) = 4) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4) ∧
    HasSum (fun j : ℕ => (factorialCarryDigit (j + 1) : ℝ) / 2 ^ (j + 1)) 4 ∧
    (∀ N, HasSum (fun j : ℕ =>
      (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (factorialCarry N : ℝ)) := @ErdosProblems.Erdos251.PaperR7.bounded_recurring_values_countermodel

end Erdos249257.ExternalVerification251PaperStatementsE
