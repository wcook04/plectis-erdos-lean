/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band e

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open Topology

namespace PalomarCorpus.E257.PaperStatementsE
open Filter
open Set
open Topology
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  sorry
/-- States lem:collapse-mech, record:257hg-i6, thm:mobius-centred-nonneg from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1) := by
  sorry
/-- States prop:collapse from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.half_of_cofinal_absolute_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      |(integerHalfCarry A N : ℝ)| ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsE
