/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.PaperCompleteR20.SignedWindow

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperCompleteR20.SignedWindow`.
-/

namespace Erdos249257.ExternalVerification251PaperStatementsD

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

end Erdos249257.ExternalVerification251PaperStatementsD
