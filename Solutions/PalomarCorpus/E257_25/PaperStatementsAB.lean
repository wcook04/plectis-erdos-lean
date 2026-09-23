/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfTrappingReturnCarry
import Solutions.PalomarCorpus.E257_25.Statement

open Matrix

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAB

theorem relationInvariantLinearChannels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (he : ∃ e : V, ev e = 1) (row : ι → V) :
    Matrix.det (fun i j : ι ↦ channel j (row i)) = 0 := by
  apply Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero <;> assumption

end PalomarCorpus.E257.PaperStatementsAB
