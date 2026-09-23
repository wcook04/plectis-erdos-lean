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
import Solutions.PalomarCorpus.E1049_01.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsG
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)

noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))

noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1

noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t

noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)

noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det

theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4 := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour

theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) := @ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all N

end PalomarCorpus.E1049.PaperStatementsG
