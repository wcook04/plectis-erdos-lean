/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.AbelControlPolygon
import ErdosProblems.Erdos1041.PaperCompleteR20.SexticSpokeWhole
import Solutions.PalomarCorpus.E1041_05.Statement

open Polynomial
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsR

theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖ := @ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole

end PalomarCorpus.E1041.PaperStatementsR
