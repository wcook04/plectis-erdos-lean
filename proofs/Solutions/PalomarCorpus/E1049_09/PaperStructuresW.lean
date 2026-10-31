/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality
import ErdosProblems.Erdos1049.QProductBoundsR10
import Solutions.PalomarCorpus.E1049_09.Statement

open Filter
open Finset
open Matrix
open scoped Topology
open scoped BigOperators
open scoped Classical

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresW
export PalomarCorpus.E1049_09.Shared (gramM qPochhammerInfinity)

theorem geometric_universality {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C κ : ℝ}
    (hlim : ∀ h : ℕ, Tendsto (fun k => a (k + h) / a k) atTop (𝓝 1))
    (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ κ) :
    HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹) (gramM q) ∧ 0 < gramM q ∧
    (∀ m : ℕ, Summable fun k => a k * q ^ ((m + 1) * k)) ∧
    Tendsto (fun N : ℕ => geomHankelDet q a N /
        (gramM q ^ 3 * q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) *
          ∏ k ∈ range N, a k))
      atTop (𝓝 1) := by
  apply ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality <;> assumption

end PalomarCorpus.E1049.PaperStructuresW
