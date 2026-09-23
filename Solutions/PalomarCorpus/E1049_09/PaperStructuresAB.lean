/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.ActualPositiveMeasureR16
import ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality
import ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisationAnalytic
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase
import ErdosProblems.Erdos1049.QProductBoundsR10
import Solutions.PalomarCorpus.E1049_09.Statement

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresAB
export PalomarCorpus.E1049_09.Shared (actualGeneratingFunction actualGeneratingTerm cK gramM qPochhammerFinite qPochhammerInfinity)

theorem sharp_fixed_base {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (γ : ℕ → ℝ)
    (hγ : ∀ w : ℝ, 0 ≤ w → w < 1 →
      HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) :
    HasProd (sharpFactor q γ) (∏' k : ℕ, sharpFactor q γ k) ∧
    0 < sharpA q γ ∧
    Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (sharpK q γ * leadC N * q ^ orderB N * qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => Real.log (actualMomentHankel q N).det -
        ((orderB N : ℝ) * Real.log q + Real.log (leadC N) +
          2 * (N : ℝ) * Real.log (qPochhammerInfinity q q) - 8 * lambertL q * Real.log N +
          Real.log (sharpK q γ))) atTop (𝓝 0) := @ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base q hq0 hq1 γ hγ

end PalomarCorpus.E1049.PaperStructuresAB
