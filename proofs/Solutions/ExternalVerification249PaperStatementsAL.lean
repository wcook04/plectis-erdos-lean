/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinaryDilationCountermodel

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinaryDilationCountermodel`.
-/

open Classical

namespace Erdos249257.ExternalVerification249PaperStatementsAL

noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0

noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)

noncomputable def xi : ℝ := tail digit 0

theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal

theorem digit_block (j : ℕ) :
    (IsSquare (j + 1) → digit (2 * j) = 1 ∧ digit (2 * j + 1) = 0) ∧
      (¬ IsSquare (j + 1) → digit (2 * j) = 0 ∧ digit (2 * j + 1) = 1) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit_block j

theorem exists_irrational_basePower_bounded_away :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n : ℕ) (z : ℤ), (1 : ℝ) / 8 ≤ |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.exists_irrational_basePower_bounded_away

theorem fract_mem_Icc_of_no_three_equal {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_mem_Icc_of_no_three_equal d hd hrun n

theorem fract_two_pow_mul_xi_mem_Icc (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * xi) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_two_pow_mul_xi_mem_Icc n

theorem irrational_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2)))
    (hper : ∀ N P : ℕ, 0 < P → ¬ ∀ k, N ≤ k → d k = d (k + P)) :
    Irrational (tail d 0) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_tail_zero d hd hrun hper

theorem irrational_xi : Irrational xi := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi

theorem no_three_consecutive_equal (n : ℕ) :
    ¬ (digit n = digit (n + 1) ∧ digit (n + 1) = digit (n + 2)) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.no_three_consecutive_equal n

theorem not_approaches_int {ε : ℝ} (hε : ε ≤ 1 / 8) :
    ¬ ∃ (n : ℕ) (z : ℤ), |(2 : ℝ) ^ n * xi - (z : ℝ)| < ε := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_approaches_int <;> assumption

theorem not_eventually_periodic (N P : ℕ) (hP : 0 < P) :
    ¬ ∀ k, N ≤ k → digit k = digit (k + P) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_eventually_periodic N P hP

theorem not_near_integer_along_powers_of_two :
    ¬ ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
        0 < |(2 : ℝ) ^ n * xi - (z : ℝ)| ∧
          |(2 : ℝ) ^ n * xi - (z : ℝ)| < 1 / (q : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_near_integer_along_powers_of_two

theorem one_div_eight_le_abs_sub_int {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * tail d 0 - (z : ℝ)| := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_abs_sub_int d hd hrun n z

theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)| := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi n z

theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed

theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8 := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc d hd hrun n

theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q q hq

end Erdos249257.ExternalVerification249PaperStatementsAL
