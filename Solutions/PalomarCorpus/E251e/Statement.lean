/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251e

Every non-theorem declaration of `PalomarCorpus/E251e/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E251.PaperStatementsE
