/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperCompleteR21.SubcriticalPerimeterPath
import Solutions.PalomarCorpus.E1041zb.Statement

open Set
open MeasureTheory
open Polynomial
open scoped ComplexConjugate
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsZB

theorem subcritical_perimeter_path_paper
    (p : Polynomial ℂ) (n : ℕ) (μ β : ℝ)
    (hmonic : p.Monic) (hsf : Squarefree p) (hdeg : p.natDegree = n) (hn : 2 ≤ n)
    (hμ : CriticalMinimum p μ) (hμpos : 0 < μ) (hβ : 0 < β)
    (hperim : ∀ σ : ℝ, 0 < σ → σ < μ → ∀ z : ℂ, ‖p.eval z‖ ≤ σ →
      μH[(1 : ℝ)] (frontier (connectedComponentIn {w : ℂ | ‖p.eval w‖ ≤ σ} z))
        ≤ ENNReal.ofReal (β * σ ^ (1 / (n : ℝ))))
    (hsplit : SubcriticalSplitExists (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ)))) :
    HasDistinctConnectionAtMost (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ))) := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path_paper <;> assumption

end PalomarCorpus.E1041.PaperStatementsZB
