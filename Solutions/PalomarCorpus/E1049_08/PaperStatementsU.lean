/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.ActualPositiveMeasureR16
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBaseShort
import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import ErdosProblems.Erdos1049.QProductBoundsR10
import Solutions.PalomarCorpus.E1049_08.Statement

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsU
export PalomarCorpus.E1049_08.Shared (actualMoment actualMomentHankel actualMomentTerm leadC qPochhammerFinite qPochhammerInfinity)

theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := @ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists q hq0 hq1

end PalomarCorpus.E1049.PaperStatementsU
