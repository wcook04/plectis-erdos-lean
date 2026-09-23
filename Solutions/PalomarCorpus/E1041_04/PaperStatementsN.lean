/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import Solutions.PalomarCorpus.E1041_04.Statement

open Set
open Metric
open AffineSubspace
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsN
export PalomarCorpus.E1041_04.Shared (SamePositiveRay)

theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ) := @ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization a b shift hab hray

end PalomarCorpus.E1041.PaperStatementsN
