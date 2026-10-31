/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperWeightedRefinementsR10
import Solutions.PalomarCorpus.E1041_06.Statement

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsL

theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := @ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le m hm c hc

end PalomarCorpus.E1041.PaperStatementsL
