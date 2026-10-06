/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.FirstHarmonicPivot
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount
import Solutions.PalomarCorpus.E249_33.Statement

open Filter
open Finset
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresT
export PalomarCorpus.E249_33.Shared (windowDiscrepancy)

theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap hgap

end PalomarCorpus.E249.PaperStructuresT
