/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_27

Every non-theorem declaration of `PalomarCorpus/E249_27/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped Classical
open scoped Nat

namespace PalomarCorpus.E249_27.Shared
/-- `α_h = (2^h - 1) S`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientAlphaShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_27.Shared

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_27.Shared (totientTail)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAM
open scoped Classical
export PalomarCorpus.E249_27.Shared (totientAlphaShift)
/-- `x` is nondyadic. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.NotDyadicRational, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j
/-- `‖x‖_{ℝ/ℤ} ≥ 1/4`, written as: every integer is at distance at least `1/4` from `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.QuarterFarFromInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|
/-- The `k`-th binary digit of `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.binaryDigitAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2
/-- The number of `N ∈ [X, 2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseCount (h X : ℕ) : ℕ :=
  ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h)).card
/-- `ρ_h(X)`: the proportion of `N ∈ [X,2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseProportion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseProportion (h X : ℕ) : ℝ := (quarterFarPhaseCount h X : ℝ) / (X : ℝ)
end PalomarCorpus.E249.PaperStatementsAM

namespace PalomarCorpus.E249.PaperStatementsBL
open scoped Classical
open Finset
export PalomarCorpus.E249_27.Shared (totientAlphaShift totientTail)
/-- First additive character of the infinite tail difference. Local copy of Erdos249257.TotientTailPeriodKiller.tailOrbitFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)
end PalomarCorpus.E249.PaperStatementsBL

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
