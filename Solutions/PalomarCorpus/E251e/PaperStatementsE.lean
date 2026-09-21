/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperBoundedCarryR7
import Solutions.PalomarCorpus.E251e.Statement

open Filter
open Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsE

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

end PalomarCorpus.E251.PaperStatementsE
