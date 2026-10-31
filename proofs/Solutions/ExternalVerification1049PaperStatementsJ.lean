/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold
import ErdosProblems.Erdos1049.PaperLinearFormsR7
import ErdosProblems.Erdos1049.RationalBaseContour

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold`,
`ErdosProblems.Erdos1049.PaperLinearFormsR7`, `ErdosProblems.Erdos1049.RationalBaseContour`.
-/

open Filter
open scoped Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStatementsJ

noncomputable def zudilinC1 : ℝ := 1091 / 2

noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v

noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)

noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0

noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)

noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b)) := @ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold a b hb hab _hcop h

theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b)) := @ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log a b hb hab _hcop h

theorem thirtyoneFour_irrational : Irrational (paperLambert ((31 : ℝ) / 4)) := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_irrational

theorem thirtyoneFour_pow_irrational (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_pow_irrational r hr

end Erdos249257.ExternalVerification1049PaperStatementsJ
