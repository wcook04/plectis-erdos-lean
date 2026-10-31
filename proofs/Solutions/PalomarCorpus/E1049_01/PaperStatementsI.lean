/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.IrrationalityExponentR11
import ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold
import ErdosProblems.Erdos1049.PaperLinearFormsR7
import ErdosProblems.Erdos1049.RationalBaseContour
import Solutions.PalomarCorpus.E1049_01.Statement

open Filter
open Set
open scoped BigOperators
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsI
export PalomarCorpus.E1049_01.Shared (approximationExponents irrationalityExponent paperLambert reducedApproximationPairs trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)

theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ)) := by
  apply ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform <;> assumption

theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301 r hr

end PalomarCorpus.E1049.PaperStatementsI
