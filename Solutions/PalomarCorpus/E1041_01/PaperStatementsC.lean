/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.HyperbolicLawOfCosines
import Solutions.PalomarCorpus.E1041_01.Statement

open Real
open Set
open MeasureTheory
open scoped UpperHalfPlane

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsC
export PalomarCorpus.E1041_01.Shared (polar polarDen_pos)

theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂) := @ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar d₁ θ₁ d₂ θ₂

theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d| := @ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dist_polar_I d θ

theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z := @ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.exists_polar z

theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I := @ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar_zero_zero

end PalomarCorpus.E1041.PaperStatementsC
