/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 11.1 to 11.5: reset bounds and finite weighted divisor sums; equivalent carry conditions at perfect-square depths; sparse and dense supports under the certificate criterion

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Set
open Topology
open Finset

namespace PalomarCorpus.E257_37.Shared
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_37.Shared

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
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi_eq_of_residues_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem Psi_eq_of_residues_eq (L D x y : ℕ) (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Psi L D x = Psi L D y := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.card_divisors_sub_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_divisors_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card - 1 : ℕ) = (n.divisors.filter (fun d => 2 ≤ d)).card := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.dvd_add_iLeast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dvd_add_iLeast (d M : ℕ) (hd : 1 ≤ d) : d ∣ M + iLeast d M := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.geometric_term_eq_zero_of_lt_iLeast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem geometric_term_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d)
    (h : L < iLeast d M) :
    (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
        / (1 - (1 / 2 : ℚ) ^ d) = 0 := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_congr in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem iLeast_congr (d M M' : ℕ) (h : M % d = M' % d) : iLeast d M = iLeast d M' := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_mem_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem iLeast_mem_Icc (d M : ℕ) (hd : 1 ≤ d) : 1 ≤ iLeast d M ∧ iLeast d M ≤ d := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount_eq_zero_of_lt_iLeast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mCount_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d) (h : L < iLeast d M) :
    mCount d M L = 0 := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.not_dvd_of_lt_iLeast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem not_dvd_of_lt_iLeast (d M i : ℕ) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hlt : i < iLeast d M) : ¬ d ∣ M + i := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_condition_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residue_condition_iff (d M i : ℕ) :
    ((i : ℤ) ≡ -(M : ℤ) [ZMOD (d : ℤ)]) ↔ d ∣ M + i := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_cutoff_reading_fails in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residue_cutoff_reading_fails :
    (∀ d ∈ Finset.Icc 2 (1 + 1), (1 : ℕ) % d = 3 % d) ∧ Theta 1 1 ≠ Theta 1 3 := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_Psi in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_eq_Psi (M L D : ℕ) (hM : 1 ≤ M) (hD : M + L ≤ D) :
    Theta L M = Psi L D M := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_eq_divisorResidueSum (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_eq_geometricForm (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
            / (1 - (1 / 2 : ℚ) ^ d) := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_eq_tsum_divisorResidue (M L : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_geometricForm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_eq_tsum_geometricForm (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          (1 / 2 : ℚ) ^ (iLeast (d + 2) M)
            * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
            / (1 - (1 / 2 : ℚ) ^ (d + 2)) := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_one_one : Theta 1 1 = 1 / 2 := by
  sorry
/-- States lem:odometer from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_three in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_one_three : Theta 1 3 = 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsL
open Filter
open Set
open Topology
export PalomarCorpus.E257_37.Shared (supportCoeff)
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
/-- States lem:sqwitness from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4 := by
  sorry
end PalomarCorpus.E257.PaperStatementsL

namespace PalomarCorpus.E257.PaperStatementsBF
open Filter
open Topology
open Finset
export PalomarCorpus.E257_37.Shared (supportCoeff)
/-- The squarefree support of Erdős #257: squarefree integers `d ≥ 2`. Local copy of ErdosProblems.Erdos257.squarefreeSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeSupport : Set ℕ := {d : ℕ | 2 ≤ d ∧ Squarefree d}
/-- States prop:squarefree from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_squarefree_support_engine_ceiling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) := by
  sorry
end PalomarCorpus.E257.PaperStatementsBF
