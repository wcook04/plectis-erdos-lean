/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249an

Every non-theorem declaration of `PalomarCorpus/E249an/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped Nat

namespace PalomarCorpus.E249.PaperStatementsAN
open Finset
open scoped Nat
/-- The paper's comparison coefficients: `c(n) = 1` when `n = k!` for some `k ≥ 1`, and `c(n) = 0` otherwise. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacCoef, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacCoef (n : ℕ) : ℤ :=
  @ite ℤ (∃ k : ℕ, 1 ≤ k ∧ n = k !) (Classical.propDecidable _) 1 0
/-- `β = ∑_{n ≥ 1} c(n)/2ⁿ` (the `n = 0` term vanishes since `k! ≥ 1`). Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacBeta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacBeta : ℝ := ∑' n : ℕ, (lacCoef n : ℝ) / 2 ^ n
/-- The paper's window discrepancy `D(h,N,L)` with the totient replaced by the comparison coefficients `c`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (lacCoef (N + h + 1 + j) - lacCoef (N + 1 + j)) * 2 ^ (L - 1 - j)
/-- The angle of the paper's `E(h,N,L)` for the comparison coefficients. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi * (((lacDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))
/-- The paper's `E(h,N,L) = e((D mod 2^L)/2^L)` for the comparison coefficients. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((lacFirstAngle h N L : ℂ) * Complex.I)
end PalomarCorpus.E249.PaperStatementsAN
