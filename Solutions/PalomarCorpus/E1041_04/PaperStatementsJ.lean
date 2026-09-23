/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import Solutions.PalomarCorpus.E1041_04.Statement

open scoped ComplexConjugate

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsJ

theorem cubic_has_safe_root_spoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := @ErdosProblems.Erdos1041.cubic_has_safe_root_spoke r s v hr hs hv

end PalomarCorpus.E1041.PaperStatementsJ
