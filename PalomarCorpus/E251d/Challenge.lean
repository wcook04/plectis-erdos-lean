/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band d

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E251.PaperStatementsD
/-- States res:signedwindow from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_consequences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem signed_two_window_consequences (D D' : ℝ) (δ s : ℤ)
    (hstep : D' = 2 * D - (δ : ℝ)) (hs : s = -1 ∨ s = 1)
    (hδ : δ = 2 * s) (hlo : (1 / 2 : ℝ) < (s : ℝ) * D)
    (hhi : (s : ℝ) * D < 1) :
    (-1 < (s : ℝ) * D' ∧ (s : ℝ) * D' < 0) ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States res:signedwindow from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem signed_two_window_iff (D D' : ℝ) (δ : ℤ)
    (heven : Even δ) (hstep : D' = 2 * D - (δ : ℝ)) :
    (|D| < 1 ∧ |D'| < 1 ∧ δ ≠ 0) ↔
      ∃ s : ℤ, (s = -1 ∨ s = 1) ∧ δ = 2 * s ∧
        (1 / 2 : ℝ) < (s : ℝ) * D ∧ (s : ℝ) * D < 1 := by
  sorry
end PalomarCorpus.E251.PaperStatementsD
