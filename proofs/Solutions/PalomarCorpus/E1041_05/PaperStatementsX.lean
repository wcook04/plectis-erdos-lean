/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.LobeAndArity
import Solutions.PalomarCorpus.E1041_05.Statement

open Polynomial
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsX
export PalomarCorpus.E1041_05.Shared (lobeComponent lobePolynomial lobeSublevel)

theorem lobe_perimeter_gt (hperim : PlanePerimeterBound) :
    ENNReal.ofReal (5 * Real.pi / 4)
      < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) := @ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.lobe_perimeter_gt hperim

theorem one_root_gamma_false (hperim : PlanePerimeterBound)
    (hGammaQuarter : Real.Gamma (1 / 4) ≤ 3.63) :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := @ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false hperim hGammaQuarter

end PalomarCorpus.E1041.PaperStatementsX
