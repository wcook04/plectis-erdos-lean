/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.2.2: equivalent quantified certificate conditions

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open scoped BigOperators

namespace PalomarCorpus.E249_10.Shared
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
end PalomarCorpus.E249_10.Shared

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_10.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_10.Shared (totientTail)
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_10.Shared (certifiedKill periodLcm totientTail windowDiscrepancy windowNumerator)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The diagonal tail difference `D(H) = R_(2H) - R_H`. Local copy of Erdos249257.PrimeJumpWindow.diagonalTailDifferenceAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H
/-- The prime-jump commutator `J(H,p) = D(pH) - p D(H)`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpTailCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H
/-- Integer depth-`L` numerator of the four-vertex commutator, with vertices ordered as `H, 2H, pH, 2pH`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpWindowCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- Real part of the first additive character of the endpoint discrepancy modulo `2^L`. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))
/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  sorry
/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry
/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry
/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282 := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ) := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L := by
  sorry
/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_four_tail_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ, 1 ≤ p ∧
      ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ) <
        (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L ∧
      (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L <
        2 ^ L - ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_10.Shared (certifiedKill periodLcm totientTail windowDiscrepancy windowNumerator)
/-- Second-difference window discrepancy `A₂ = A(h, N+h, L) - A(h, N, L)`: the depth-`L` truncation of `2^L·((R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N))`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy2, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L
/-- The decidable rank-2 certificate: the residue of `A₂` modulo `2^L` avoids the radius-`2(N+2h+L+2)` neighbourhood of `0`. The doubled radius pays for two window truncations; in exchange the second difference cancels the whole `H·C` clean shadow on the lcm cone. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedRank2Kill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_forces_four_tail_diagonals_integral
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ p : ℕ, 0 < p →
      (totientTail (2 * periodLcm t) - totientTail (periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
        (totientTail (2 * (p * periodLcm t)) - totientTail (p * periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9 := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2) := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2 := by
  sorry
/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.windowDiscrepancy_diagonal_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem windowDiscrepancy_diagonal_eq (M L : ℕ) :
    windowDiscrepancy M M L =
      (windowNumerator (2 * M) L : ℤ) - (windowNumerator M L : ℤ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_10.Shared (periodLcm totientTail windowNumerator)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridNumerator (H L q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 L, Nat.totient (q * H + j) * 2 ^ (L - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridCertificate (H L : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((paperGridNumerator H L qi : ℤ) - paperGridNumerator H L qj) % 2 ^ L
/-- States catalogue:cert:b10a, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b10a, catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1 := by
  sorry
/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_cos_pi_div_eight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem nine_tenths_lt_cos_pi_div_eight : (9 / 10 : ℝ) < Real.cos (Real.pi / 8) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ
