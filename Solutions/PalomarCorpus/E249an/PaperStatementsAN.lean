/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR21.LacunaryFactorialBlockNorm
import Solutions.PalomarCorpus.E249an.Statement

open Finset
open scoped Nat

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAN

theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8) := @ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt

theorem irrational_lacBeta : Irrational lacBeta := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta

theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!) := @ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series

theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds n hn

theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := @ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap h X hh hX

theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := @ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails h X L hh hX hroom

end PalomarCorpus.E249.PaperStatementsAN
