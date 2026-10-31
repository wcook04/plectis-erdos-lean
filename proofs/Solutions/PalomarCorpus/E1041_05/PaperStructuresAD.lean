/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.LobeAndArity
import ErdosProblems.Erdos1041.PaperCompleteR21.LobeUnconditional
import Solutions.PalomarCorpus.E1041_05.Statement

open Polynomial
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStructuresAD
export PalomarCorpus.E1041_05.Shared (lobeComponent lobePolynomial lobeSublevel)

theorem one_root_gamma_false_unconditional :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := @ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false_unconditional

end PalomarCorpus.E1041.PaperStructuresAD
