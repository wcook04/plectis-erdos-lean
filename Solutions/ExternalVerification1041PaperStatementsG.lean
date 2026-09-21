/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperStraightObstructions

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperStraightObstructions`.
-/

open Polynomial

namespace Erdos249257.ExternalVerification1041PaperStatementsG

theorem complete_straight_path_obstructions :
    (∃ f : ℂ[X], f.Monic ∧ f.natDegree = 5 ∧
      (∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1) ∧
      ∃ c w : ℂ, f.derivative.eval c = 0 ∧ f.eval c ≠ 0 ∧ f.eval w = 0 ∧
        (∀ z : ℂ, f.eval z = 0 → z ≠ w → ‖c - w‖ < ‖c - z‖) ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 < ‖f.eval (c + (t : ℂ) * (w - c))‖) ∧
    (∃ g : ℂ[X], g.Monic ∧ g.natDegree = 3 ∧
      (∀ z : ℂ, g.eval z = 0 → ‖z‖ < 1) ∧
      ∀ z w : ℂ, g.eval z = 0 → g.eval w = 0 → z ≠ w →
        1 < ‖g.eval ((z + w) / 2)‖) := @ErdosProblems.Erdos1041.PaperStraightObstructions.complete_straight_path_obstructions

end Erdos249257.ExternalVerification1041PaperStatementsG
