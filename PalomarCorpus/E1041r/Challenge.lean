/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band r

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Finset

namespace PalomarCorpus.E1041.PaperStatementsR
open Polynomial
open Finset
/-- The stored sextic guardrail family `f_r z = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6`. Local copy of ErdosProblems.Erdos1041.AbelControlPolygon.sextic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sextic (r z : ℂ) : ℂ :=
  z ^ 6 + (1 / 5) * r ^ 2 * z ^ 4 - (1 / 5) * r ^ 4 * z ^ 2 - r ^ 6
/-- States res:sextic-spoke from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖ := by
  sorry
end PalomarCorpus.E1041.PaperStatementsR
