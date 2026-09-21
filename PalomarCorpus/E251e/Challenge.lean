/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band e

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsE
open Filter
open Topology
open scoped BigOperators
/-- The special indices of the printed bounded construction. Local copy of ErdosProblems.Erdos251.PaperR7.IsFactorialSpike, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsFactorialSpike (n : ℕ) : Prop := ∃ k : ℕ, 3 ≤ k ∧ n = k.factorial
/-- U_0=4; at factorials k! with k>=3 the carry is 6, otherwise it is 4. Local copy of ErdosProblems.Erdos251.PaperR7.factorialCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialCarry (n : ℕ) : ℤ := by
  classical
  exact if IsFactorialSpike n then 6 else 4
/-- a_0 is unused. At every positive index this is 2 U_(n-1) - U_n. Local copy of ErdosProblems.Erdos251.PaperR7.factorialCarryDigit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialCarryDigit (n : ℕ) : ℤ :=
  if n = 0 then 0 else 2 * factorialCarry (n - 1) - factorialCarry n
/-- States long251:xr:boundedpolignac from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.bounded_recurring_values_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_recurring_values_countermodel :
    (∀ n, 1 ≤ n → factorialCarryDigit n = 2 ∨
      factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8) ∧
    (∀ k, 3 ≤ k → factorialCarryDigit k.factorial = 2 ∧
      factorialCarryDigit (2 * k.factorial) = 4) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4) ∧
    HasSum (fun j : ℕ => (factorialCarryDigit (j + 1) : ℝ) / 2 ^ (j + 1)) 4 ∧
    (∀ N, HasSum (fun j : ℕ =>
      (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (factorialCarry N : ℝ)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsE
