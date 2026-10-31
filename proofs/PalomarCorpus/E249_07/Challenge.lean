/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.2.1: initial implications (part 1 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open Filter
open Topology
open Classical
open Module
open Matrix
open ArithmeticFunction
open scoped BigOperators

namespace PalomarCorpus.E249_07.Shared
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
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
end PalomarCorpus.E249_07.Shared

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_07.Shared (certifiedKill totientTail windowDiscrepancy)
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
export PalomarCorpus.E249_07.Shared (certifiedKill totientTail windowDiscrepancy)
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
/-- States catalogue:mob:a1a from the long record for Erdős problem #249. Transported from Erdos249257.totient_series_eq_half_add_moebius_mersenne_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_eq_half_add_moebius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from Erdos249257.positive_rational_difference_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positive_rational_difference_lower_bound
    {whole pfx : ℚ} (hpositive : pfx < whole) :
    (1 : ℝ) /
        (((whole.den * pfx.den : ℕ) : ℝ)) ≤
      (whole : ℝ) - (pfx : ℝ) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den := by
  sorry
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
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8 := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAL

namespace PalomarCorpus.E249.PaperStructuresP
open Module
open Matrix
/-- A square nonzero evaluation minor. This is the exact finite object needed to turn number-theoretic row construction into linear independence. Local copy of Erdos249257.SeparatedMinorCertificate, restated so the compared statements elaborate against Mathlib alone. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
/-- States catalogue:cert:d3 from the long record for Erdős problem #249. Transported from Erdos249257.linearIndependent_of_separatedMinorCertificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := by
  sorry
end PalomarCorpus.E249.PaperStructuresP

namespace PalomarCorpus.E249.PaperStatementsAP
open ArithmeticFunction
/-- States catalogue:mob:a1a from the long record for Erdős problem #249. Transported from MersenneLambertLadder.tsum_moebius_lambert_sq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAP

namespace PalomarCorpus.E249.PaperStatementsH
open scoped BigOperators
/-- States catalogue:mob:a1b from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsH

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.pair_divisibility_mass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  sorry
/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_geometric_multiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States catalogue:mob:a8 from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK
