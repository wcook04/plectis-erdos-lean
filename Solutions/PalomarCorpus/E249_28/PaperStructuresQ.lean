/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.FirstHarmonicPivot
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCut
import Solutions.PalomarCorpus.E249_28.Statement

open Finset
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresQ

theorem prop_dickman (h s : ℕ) :
    (∀ X, AdmissibleDepth h s X (minimalDepth h s X) ∧
        ∀ L, AdmissibleDepth h s X L → minimalDepth h s X ≤ L) ∧
    (∀ X, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X N, 0 < X → N ∈ Ico X (2 * X) → N ∉ pivotSupplierBases X (minimalDepth h s X) s →
      ∀ hn : 1 < N + minimalOffset h s X,
        (((N + minimalOffset h s X).primeFactors.max'
            (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) ≤ minimalCut h s X) ∧
    (∀ X, 0 < X →
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        ≤ (smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) ∧
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) ∧
    (∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X ∧
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        < 8 / 25 * X) := @ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman h s

end PalomarCorpus.E249.PaperStructuresQ
