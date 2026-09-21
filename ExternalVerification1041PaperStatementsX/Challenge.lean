/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR21.LobeAndArity`.
-/

open Polynomial
open Set

namespace Erdos249257.ExternalVerification1041PaperStatementsX

noncomputable def PlanePerimeterBound : Prop :=
  ∀ (A : Set ℂ) (x : ℂ) (ρ : ℝ), 0 ≤ ρ → Bornology.IsBounded A →
    Metric.closedBall x ρ ⊆ A →
    ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (frontier A)

noncomputable def lobePolynomial : ℂ[X] := X ^ 8 - C (3 / 2) * X

noncomputable def lobeSublevel : Set ℂ := {z : ℂ | ‖lobePolynomial.eval z‖ ≤ 1}

noncomputable def lobeComponent : Set ℂ := connectedComponentIn lobeSublevel 0

/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobe_perimeter_gt in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lobe_perimeter_gt (hperim : PlanePerimeterBound) :
    ENNReal.ofReal (5 * Real.pi / 4)
      < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) := by
  sorry

/-- States res:one-root-gamma-false from the short record for Erdős problem #1041. Transported
from ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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

end Erdos249257.ExternalVerification1041PaperStatementsX
