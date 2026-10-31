/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCompleteR20.FiniteSeparation
import Solutions.PalomarCorpus.E251_04.Statement

open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsB

theorem finite_separation_complete (D : ℝ) (S R : ℕ → ℝ)
    (hR : ∀ L, 0 ≤ R L) (herr : ∀ L, |D-S L| ≤ R L)
    (hlim : Tendsto R atTop (𝓝 0)) :
    D ∉ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ L, R L < Metric.infDist (S L) (Set.range ((↑) : ℤ → ℝ)) := @ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete D S R hR herr hlim

theorem one_tail_signed_certificate (D D' : ℝ) (s A B Q : ℤ)
    (hs : s = -1 ∨ s = 1) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hstep : D' = 2 * D - (2 * s : ℤ))
    (herr : |(Q : ℝ) * D - A| ≤ B)
    (hlo : 2 * s * A - Q > 2 * B) (hhi : Q - s * A > B) :
    ((1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1) ∧ |D'| < 1 ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate D D' s A B Q hs hQ hB hstep herr hlo hhi

end PalomarCorpus.E251.PaperStatementsB
