/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import Solutions.PalomarCorpus.E1041_05.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsK

theorem exists_two_roots_dist_sum_le_two_mul_geomMean
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := @ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean n hn z c hne hcrit r hr hrn

end PalomarCorpus.E1041.PaperStatementsK
