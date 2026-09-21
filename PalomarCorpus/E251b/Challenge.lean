/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band b

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology

namespace PalomarCorpus.E251.PaperStatementsB
open Filter
open Topology
/-- States long251:res:complete-truncation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_separation_complete (D : ℝ) (S R : ℕ → ℝ)
    (hR : ∀ L, 0 ≤ R L) (herr : ∀ L, |D-S L| ≤ R L)
    (hlim : Tendsto R atTop (𝓝 0)) :
    D ∉ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ L, R L < Metric.infDist (S L) (Set.range ((↑) : ℤ → ℝ)) := by
  sorry
/-- States long251:res:one-tail-certificate from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_tail_signed_certificate (D D' : ℝ) (s A B Q : ℤ)
    (hs : s = -1 ∨ s = 1) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hstep : D' = 2 * D - (2 * s : ℤ))
    (herr : |(Q : ℝ) * D - A| ≤ B)
    (hlo : 2 * s * A - Q > 2 * B) (hhi : Q - s * A > B) :
    ((1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1) ∧ |D'| < 1 ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E251.PaperStatementsB
