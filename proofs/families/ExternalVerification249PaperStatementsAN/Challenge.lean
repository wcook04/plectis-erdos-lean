/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.PaperCompleteR21.LacunaryFactorialBlockNorm`.
-/

open Finset
open scoped Nat

namespace Erdos249257.ExternalVerification249PaperStatementsAN

noncomputable def lacCoef (n : ℕ) : ℤ :=
  @ite ℤ (∃ k : ℕ, 1 ≤ k ∧ n = k !) (Classical.propDecidable _) 1 0

noncomputable def lacBeta : ℝ := ∑' n : ℕ, (lacCoef n : ℝ) / 2 ^ n

noncomputable def lacDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (lacCoef (N + h + 1 + j) - lacCoef (N + 1 + j)) * 2 ^ (L - 1 - j)

noncomputable def lacFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi * (((lacDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))

noncomputable def lacFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((lacFirstAngle h N L : ℂ) * Complex.I)

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8) := by
  sorry

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_lacBeta : Irrational lacBeta := by
  sorry

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!) := by
  sorry

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ) := by
  sorry

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
  sorry

/-- States thm:lacunary from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAN
