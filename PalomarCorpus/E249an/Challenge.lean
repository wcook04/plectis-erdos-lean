/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band n

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Finset
open scoped Nat

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
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_lacBeta : Irrational lacBeta := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := by
  sorry
end PalomarCorpus.E249.PaperStatementsAN
