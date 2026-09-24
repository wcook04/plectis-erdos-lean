/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.PaperR17.SourceConsumers
import Mathlib
import Solutions.PalomarCorpus.E1049_07.Statement

open scoped BigOperators

namespace PalomarCorpus.E1049.RationalBaseRegion

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

noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

noncomputable def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

noncomputable def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)

noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)

private theorem definitions_match_paperLambert (x : ℝ) :
    paperLambert x = ErdosProblems.Erdos1049.PaperR7.paperLambert x := rfl

private theorem definitions_match_region (a b : ℕ) :
    ZudilinContourRegion a b =
      ErdosProblems.Erdos1049.ZudilinContourRegion a b := rfl

theorem rational_base_region (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  simpa only [definitions_match_paperLambert, definitions_match_region] using
    ErdosProblems.Erdos1049.PaperR17.rational_base_region a b hb hab hr

theorem thirtyone_four_powers (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := by
  simpa only [definitions_match_paperLambert] using
    ErdosProblems.Erdos1049.PaperR17.thirtyone_four_powers r hr

theorem thirtyone_four : Irrational (paperLambert ((31 : ℝ) / 4)) := by
  simpa only [definitions_match_paperLambert] using
    ErdosProblems.Erdos1049.PaperR17.thirtyone_four

theorem rational_base_measure (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert ((a : ℝ) / b)) ≤
      rationalBaseMeasureBound a b := by
  simpa only [paperLambert, trigammaSeries, zudilinJTerm, zudilinJ, zudilinC1,
    zudilinC0, zudilinContour, ZudilinContourRegion, reducedApproximationPairs,
    approximationExponents, irrationalityExponent, rationalBaseMeasureBound,
    ErdosProblems.Erdos1049.PaperR7.paperLambert,
    ErdosProblems.Erdos1049.trigammaSeries, ErdosProblems.Erdos1049.zudilinJTerm,
    ErdosProblems.Erdos1049.zudilinJ, ErdosProblems.Erdos1049.zudilinC1,
    ErdosProblems.Erdos1049.zudilinC0, ErdosProblems.Erdos1049.zudilinContour,
    ErdosProblems.Erdos1049.ZudilinContourRegion,
    ErdosProblems.Erdos1049.PaperR11.reducedApproximationPairs,
    ErdosProblems.Erdos1049.PaperR11.approximationExponents,
    ErdosProblems.Erdos1049.PaperR11.irrationalityExponent,
    ErdosProblems.Erdos1049.PaperR10.rationalBaseMeasureBound] using
    ErdosProblems.Erdos1049.PaperR17.rational_base_measure a b hb hab hr

theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b)
    (hab : b < a) (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b := by
  simpa only [paperLambert, trigammaSeries, zudilinJTerm, zudilinJ, zudilinC1,
    zudilinC0, zudilinContour, ZudilinContourRegion, reducedApproximationPairs,
    approximationExponents, irrationalityExponent, rationalBaseMeasureBound,
    ErdosProblems.Erdos1049.PaperR7.paperLambert,
    ErdosProblems.Erdos1049.trigammaSeries, ErdosProblems.Erdos1049.zudilinJTerm,
    ErdosProblems.Erdos1049.zudilinJ, ErdosProblems.Erdos1049.zudilinC1,
    ErdosProblems.Erdos1049.zudilinC0, ErdosProblems.Erdos1049.zudilinContour,
    ErdosProblems.Erdos1049.ZudilinContourRegion,
    ErdosProblems.Erdos1049.PaperR11.reducedApproximationPairs,
    ErdosProblems.Erdos1049.PaperR11.approximationExponents,
    ErdosProblems.Erdos1049.PaperR11.irrationalityExponent,
    ErdosProblems.Erdos1049.PaperR10.rationalBaseMeasureBound] using
    ErdosProblems.Erdos1049.PaperR17.rational_base_power_measure
      a b r hb hab hr hregion

theorem thirtyone_four_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 := by
  simpa only [paperLambert, reducedApproximationPairs, approximationExponents,
    irrationalityExponent, ErdosProblems.Erdos1049.PaperR7.paperLambert,
    ErdosProblems.Erdos1049.PaperR11.reducedApproximationPairs,
    ErdosProblems.Erdos1049.PaperR11.approximationExponents,
    ErdosProblems.Erdos1049.PaperR11.irrationalityExponent] using
    ErdosProblems.Erdos1049.PaperR17.thirtyone_four_power_measure_lt_301 r hr

theorem thirtyone_four_power_measure_lt_paper_fraction
    (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) <
      (2981509 : ℝ) / 9909 := by
  simpa only [paperLambert, reducedApproximationPairs, approximationExponents,
    irrationalityExponent, ErdosProblems.Erdos1049.PaperR7.paperLambert,
    ErdosProblems.Erdos1049.PaperR11.reducedApproximationPairs,
    ErdosProblems.Erdos1049.PaperR11.approximationExponents,
    ErdosProblems.Erdos1049.PaperR11.irrationalityExponent] using
    ErdosProblems.Erdos1049.PaperR17.thirtyone_four_power_measure_lt_paper_fraction r hr

end PalomarCorpus.E1049.RationalBaseRegion
