/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6.1 to 6.2: unconditional structure and finite examples; definitions and elementary identities

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction
open Finset
open Filter
open Topology
open Classical

namespace PalomarCorpus.E249_06.Shared
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScalesThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepthThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0
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
end PalomarCorpus.E249_06.Shared

namespace PalomarCorpus.E249.PaperStatementsAF
open scoped BigOperators
open Matrix
open ArithmeticFunction
/-- States catalogue:mob:d3 from the long record for Erdős problem #249. Transported from Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAF

namespace PalomarCorpus.E249.PaperStatementsG
export PalomarCorpus.E249_06.Shared (diagonalPincerCertificateScalesThroughT64 diagonalPincerKillDepthThroughT64)
/-- The arguments of the totient evaluations in a family of two windows. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.certificateWindowIndices, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificateWindowIndices (H N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).biUnion fun h =>
    (Finset.range L).image (fun j => N + 1 + j) ∪
      (Finset.range L).image (fun j => N + h + 1 + j)
/-- States catalogue:cert:b11, prop:B11-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26] := by
  sorry
/-- States catalogue:cert:a12 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25 := by
  sorry
/-- States catalogue:cert:a11 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24 := by
  sorry
end PalomarCorpus.E249.PaperStatementsG

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill diagonalPincerCertificateScalesThroughT64 diagonalPincerKillDepthThroughT64 windowDiscrepancy)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- States catalogue:cert:b11, prop:B11-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem historical_table_and_complete_band :
    (∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)) ∧
    (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) := by
  sorry
/-- States catalogue:cert:a12 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificates_and_exclusions in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sixteen_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 → r.den ∣ 2 ^ 14 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) := by
  sorry
/-- States catalogue:cert:a11 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.small_certificates_and_exclusions in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem small_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 8 → r.den ∣ 2 ^ 12 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsI

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill totientTail windowDiscrepancy)
/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L := by
  sorry
/-- States catalogue:cert:a7 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:a2 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
    ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry
/-- States catalogue:cert:a6 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill totientTail windowDiscrepancy)
/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L := by
  sorry
/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L := by
  sorry
/-- States catalogue:cert:a2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N) := by
  sorry
/-- States catalogue:cert:a6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
/-- States catalogue:cert:d1, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_int_mul_near_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_pow_mul_near_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_base_powers in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_near_integer_base_powers (b₀ : ℕ) (hb : 2 ≤ b₀) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_multiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_near_integer_multiples {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)| := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- **The paper's binary example.** Reading the expansion two digits at a time, the block with index `k ≥ 1` is `10` when `k` is a perfect square and `01` otherwise. Position `n` sits inside the block with index `n / 2 + 1`, and is that block's first digit exactly when `n` is even. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0
/-- The real number whose binary digits, read from position `n` on, are `d n, d (n+1), d (n+2), …`. For `n = 0` this is the number itself; for general `n` it is the tail left after `n` binary shifts. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)
/-- **ξ**, the number of the paper's binary example. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := tail digit 0
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit_block in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem digit_block (j : ℕ) :
    (IsSquare (j + 1) → digit (2 * j) = 1 ∧ digit (2 * j + 1) = 0) ∧
      (¬ IsSquare (j + 1) → digit (2 * j) = 0 ∧ digit (2 * j + 1) = 1) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.exists_irrational_basePower_bounded_away in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_irrational_basePower_bounded_away :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n : ℕ) (z : ℤ), (1 : ℝ) / 8 ≤ |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_mem_Icc_of_no_three_equal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fract_mem_Icc_of_no_three_equal {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_two_pow_mul_xi_mem_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fract_two_pow_mul_xi_mem_Icc (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * xi) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_tail_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2)))
    (hper : ∀ N P : ℕ, 0 < P → ¬ ∀ k, N ≤ k → d k = d (k + P)) :
    Irrational (tail d 0) := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_xi : Irrational xi := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.no_three_consecutive_equal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_three_consecutive_equal (n : ℕ) :
    ¬ (digit n = digit (n + 1) ∧ digit (n + 1) = digit (n + 2)) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_approaches_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem not_approaches_int {ε : ℝ} (hε : ε ≤ 1 / 8) :
    ¬ ∃ (n : ℕ) (z : ℤ), |(2 : ℝ) ^ n * xi - (z : ℝ)| < ε := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_eventually_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem not_eventually_periodic (N P : ℕ) (hP : 0 < P) :
    ¬ ∀ k, N ≤ k → digit k = digit (k + P) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_near_integer_along_powers_of_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem not_near_integer_along_powers_of_two :
    ¬ ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
        0 < |(2 : ℝ) ^ n * xi - (z : ℝ)| ∧
          |(2 : ℝ) ^ n * xi - (z : ℝ)| < 1 / (q : ℝ) := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_abs_sub_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_eight_le_abs_sub_int {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * tail d 0 - (z : ℝ)| := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)| := by
  sorry
end PalomarCorpus.E249.PaperStatementsAL
