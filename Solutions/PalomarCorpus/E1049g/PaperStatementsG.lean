/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.AllRow.Producer
import ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold
import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos1049.RationalBaseLambert
import ErdosProblems.Erdos1049.ZudilinSharpHankelCoefficient
import Solutions.PalomarCorpus.E1049g.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsG

theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4 := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour

theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) := @ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all N

end PalomarCorpus.E1049.PaperStatementsG
