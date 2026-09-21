/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band x

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
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
/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobe_perimeter_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lobe_perimeter_gt (hperim : PlanePerimeterBound) :
    ENNReal.ofReal (5 * Real.pi / 4)
      < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) := by
  sorry
/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_root_gamma_false (hperim : PlanePerimeterBound)
    (hGammaQuarter : Real.Gamma (1 / 4) ≤ 3.63) :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsX
