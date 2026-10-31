/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCompleteR20.SignedWindow
import Solutions.PalomarCorpus.E251_05.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsD

theorem signed_two_window_consequences (D D' : ℝ) (δ s : ℤ)
    (hstep : D' = 2 * D - (δ : ℝ)) (hs : s = -1 ∨ s = 1)
    (hδ : δ = 2 * s) (hlo : (1 / 2 : ℝ) < (s : ℝ) * D)
    (hhi : (s : ℝ) * D < 1) :
    (-1 < (s : ℝ) * D' ∧ (s : ℝ) * D' < 0) ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  apply ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_consequences <;> assumption

theorem signed_two_window_iff (D D' : ℝ) (δ : ℤ)
    (heven : Even δ) (hstep : D' = 2 * D - (δ : ℝ)) :
    (|D| < 1 ∧ |D'| < 1 ∧ δ ≠ 0) ↔
      ∃ s : ℤ, (s = -1 ∨ s = 1) ∧ δ = 2 * s ∧
        (1 / 2 : ℝ) < (s : ℝ) * D ∧ (s : ℝ) * D < 1 := by
  apply ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_iff <;> assumption

end PalomarCorpus.E251.PaperStatementsD
