/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.KernelCarryRank
import ErdosProblems.Erdos269.PaperR7AnalyticInterfaces
import ErdosProblems.Erdos269.PaperR8UniformRank
import Solutions.PalomarCorpus.E269e.Statement

open Set
open Metric
open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsE

theorem uniform_rank_complete {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal ((1 - (r : ℝ)⁻¹) / 2) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    ∃ A : FiniteRankMatrix,
      (∀ i j, A.val i j = (1 + (r : ℝ)⁻¹) / 2) ∧
      uniformError (realCarryMatrix p q r) A.val =
        (⨅ F : FiniteRankMatrix, uniformError (realCarryMatrix p q r) F.val) := @ErdosProblems.Erdos269.PaperR8.uniform_rank_complete p q r hp hq hr hpr hqr

end PalomarCorpus.E269.PaperStatementsE
