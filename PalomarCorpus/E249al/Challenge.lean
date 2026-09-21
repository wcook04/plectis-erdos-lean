/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band l

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Classical

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- **The paper's binary example.** Reading the expansion two digits at a time, the block with index `k ≥ 1` is `10` when `k` is a perfect square and `01` otherwise. Position `n` sits inside the block with index `n / 2 + 1`, and is that block's first digit exactly when `n` is even. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0
/-- The real number whose binary digits, read from position `n` on, are `d n, d (n+1), d (n+2), …`. For `n = 0` this is the number itself; for general `n` it is the tail left after `n` binary shifts. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)
/-- **ξ**, the number of the paper's binary example. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := tail digit 0
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ) := by
  sorry
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
