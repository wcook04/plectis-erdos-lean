/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_45

Every non-theorem declaration of `PalomarCorpus/E257_45/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open Topology
open Finset

namespace PalomarCorpus.E257_45.Shared
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_45.Shared

namespace PalomarCorpus.E257.PaperStatementsAA
/-- `Ψ_{L,D}(x) = ∑_{d=2}^{D} ∑_{i=1}^{L} 2^{-i} 1_{d ∣ x+i}`, the finite-cutoff residue form (paper line 7966). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Psi (L D x : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 2 D, ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ x + i), (1 / 2 : ℚ) ^ i
/-- Definition `defn:theta` (line 7850): the short-window divisor phase `Θ_L(M) = ∑_{i=1}^{L} (τ(M+i) − 1) 2^{-i}`, where `τ` is the number-of-divisors function. For `M ≥ 1` and `1 ≤ i` the truncated subtraction is the honest `τ(M+i) − 1` because `M + i ≥ 1`; see `card_divisors_sub_one` for the paper's own gloss `τ(n) − 1 = #{d ≥ 2 : d ∣ n}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Theta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Theta (L M : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 L, (((M + i).divisors.card - 1 : ℕ) : ℚ) * (1 / 2 : ℚ) ^ i
/-- `i_d(M)`: the least `i ≥ 1` with `d ∣ M + i`. Equal to `d − (M mod d)`, with value `d` when the remainder is zero, and manifestly a function of `M mod d`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def iLeast (d M : ℕ) : ℕ := d - M % d
/-- `m_d = #{1 ≤ i ≤ L : d ∣ M + i}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mCount (d M L : ℕ) : ℕ := ((Finset.Icc 1 L).filter (fun i => d ∣ M + i)).card
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsL
open Filter
open Set
open Topology
export PalomarCorpus.E257_45.Shared (supportCoeff)
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.PaperStatementsL

namespace PalomarCorpus.E257.PaperStatementsBF
open Filter
open Topology
open Finset
export PalomarCorpus.E257_45.Shared (supportCoeff)
/-- The squarefree support of Erdős #257: squarefree integers `d ≥ 2`. Local copy of ErdosProblems.Erdos257.squarefreeSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeSupport : Set ℕ := {d : ℕ | 2 ≤ d ∧ Squarefree d}
end PalomarCorpus.E257.PaperStatementsBF
