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
open scoped Classical

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresT
export PalomarCorpus.E249_33.Shared (windowDiscrepancy)

theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  have hsup (X L s : ℕ) :
      pivotSupplierBases X L s = Erdos249257.pivotSupplierBases X L s := by
    ext N
    simp only [pivotSupplierBases, Erdos249257.pivotSupplierBases, Finset.mem_filter] <;> rfl
  have hgood (X L s : ℕ) (η : ℝ) :
      pivotGoodBases X L s η = Erdos249257.pivotGoodBases X L s η := by
    ext N
    simp only [pivotGoodBases, Erdos249257.pivotGoodBases, Finset.mem_filter, hsup] <;> rfl
  have hdepth (h s X : ℕ) :
      minimalDepth h s X = ErdosProblems.Erdos249.PaperCompleteR21.minimalDepth h s X := by
    unfold minimalDepth
    apply Nat.le_antisymm
    · exact Nat.find_min' _
        (ErdosProblems.Erdos249.PaperCompleteR21.minimalDepth_admissible h s X)
    · exact ErdosProblems.Erdos249.PaperCompleteR21.minimalDepth_le
        (Nat.find_spec (exists_admissibleDepth h s X))
  have hexp (h N L : ℕ) :
      windowFirstExp h N L = Erdos249257.TotientTailPeriodKiller.windowFirstExp h N L := by
    rfl
  apply ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap
  intro h hh A
  obtain ⟨X, hX, hg⟩ := hgap h hh A
  refine ⟨X, hX, ?_⟩
  simpa only [hdepth, hgood, hexp] using hg

end PalomarCorpus.E249.PaperStructuresT
