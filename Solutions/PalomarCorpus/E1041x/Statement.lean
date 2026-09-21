/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041x

Every non-theorem declaration of `PalomarCorpus/E1041x/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open Set

namespace PalomarCorpus.E1041.PaperStatementsX
open Polynomial
open Set
/-- The external classical input for the perimeter clause: for a bounded planar set containing a closed disc of radius `ρ`, the one-dimensional Hausdorff measure of the boundary is at least the circumference `2πρ`. This is absent from Mathlib (which has `μH[1]` but no perimeter-monotonicity or isoperimetric inequality) and from this tree. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.PlanePerimeterBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PlanePerimeterBound : Prop :=
  ∀ (A : Set ℂ) (x : ℂ) (ρ : ℝ), 0 ≤ ρ → Bornology.IsBounded A →
    Metric.closedBall x ρ ⊆ A →
    ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (frontier A)
/-- `p(z) = z^8 - (3/2)z`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobePolynomial : ℂ[X] := X ^ 8 - C (3 / 2) * X
/-- The closed unit sublevel set of `p`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobeSublevel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobeSublevel : Set ℂ := {z : ℂ | ‖lobePolynomial.eval z‖ ≤ 1}
/-- `C`: the connected component of `{|p| ≤ 1}` containing the origin. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobeComponent, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lobeComponent : Set ℂ := connectedComponentIn lobeSublevel 0
end PalomarCorpus.E1041.PaperStatementsX
