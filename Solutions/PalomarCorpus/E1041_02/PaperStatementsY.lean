/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.ConstantFactorAreaCriteria
import Solutions.PalomarCorpus.E1041_02.Statement

open Polynomial
open scoped NNReal
open scoped ENNReal
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsY
export PalomarCorpus.E1041_02.Shared (cfaJoinedBelow)

theorem cfa_capacity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {κ : ℝ} {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hκ0 : 0 ≤ κ) (hκ : κ ≤ cfaTau k₀)
    (hext : CFACapacityConstruction n f z κ k₀) :
    cfaJoinedBelow f z 1 2 := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.cfa_capacity_criterion <;> assumption

end PalomarCorpus.E1041.PaperStatementsY
