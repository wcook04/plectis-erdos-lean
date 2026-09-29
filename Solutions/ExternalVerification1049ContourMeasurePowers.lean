/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.PaperR17.FCContourMeasureAdapter

set_option autoImplicit false

namespace ExternalVerification1049ContourMeasurePowers

open scoped BigOperators

noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)

noncomputable def trigammaSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

noncomputable def zudilinJTerm (u v : ℝ) : ℝ :=
  trigammaSeries u - trigammaSeries v

noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

noncomputable def zudilinC1 : ℝ := 1091 / 2
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)

noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)

theorem rational_base_contour_measure
    (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hregion : ZudilinContourRegion a b) :
    ∀ r : ℕ, 0 < r →
      Irrational (paperLambert (((a : ℝ) / b) ^ r)) ∧
      irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
        rationalBaseMeasureBound a b  := by
  change ErdosProblems.Erdos1049.ZudilinContourRegion a b at hregion
  change ∀ r : ℕ, 0 < r →
    Irrational (ErdosProblems.Erdos1049.PaperR7.paperLambert (((a : ℝ) / b) ^ r)) ∧
    ErdosProblems.Erdos1049.PaperR11.irrationalityExponent
      (ErdosProblems.Erdos1049.PaperR7.paperLambert (((a : ℝ) / b) ^ r)) ≤
      ErdosProblems.Erdos1049.PaperR10.rationalBaseMeasureBound a b
  exact ErdosProblems.Erdos1049.PaperR17.rational_base_contour_measure a b hb hab hregion

end ExternalVerification1049ContourMeasurePowers
