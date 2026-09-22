/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContourConstants
import ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogConstants
import ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold
import ErdosProblems.Erdos1049.PaperOmegaIndicatorR7
import ErdosProblems.Erdos1049.RationalBaseContour
import Solutions.PalomarCorpus.E1049c.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsC

theorem contour_enclosure :
    (40568302138406054100 : ℝ) / 10 ^ 20 ≤ zudilinContour ∧
      zudilinContour ≤ (40568302138406054104 : ℝ) / 10 ^ 20 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.contour_enclosure

theorem four_rpow_mu_lt_thirtyOne : (4 : ℝ) ^ paperMu < 31 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.four_rpow_mu_lt_thirtyOne

theorem printed_contour :
    (40568302138406054 : ℝ) / 10 ^ 17 < zudilinContour ∧
      zudilinContour < (40568302138406055 : ℝ) / 10 ^ 17 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour

theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short

theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu

theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu

theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries x hx

theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh x hx

theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure

theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure

theorem paperBvMu_eq : paperBvMu = 1 / (1 / 2 - 1 / Real.pi ^ 2) := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu_eq

theorem printed_bvMu :
    (2508284761994 : ℝ) / 10 ^ 12 < paperBvMu ∧
      paperBvMu < (2508284761995 : ℝ) / 10 ^ 12 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bvMu

theorem printed_bv_cutoff :
    (3986788163576622 : ℝ) / 10 ^ 16 < 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 < (3986788163576623 : ℝ) / 10 ^ 16 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bv_cutoff

theorem printed_four_rpow_bvMu :
    (32369642 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperBvMu ∧
      (4 : ℝ) ^ paperBvMu < (32369643 : ℝ) / 10 ^ 6 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_four_rpow_bvMu

theorem printed_log_ratio :
    (4036981731641997 : ℝ) / 10 ^ 16 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (4036981731641998 : ℝ) / 10 ^ 16 := @ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_log_ratio

theorem inv_bvMu_eq : 1 / bvMu = 1 / 2 - 1 / Real.pi ^ 2 := @ErdosProblems.Erdos1049.PaperCompleteR21.inv_bvMu_eq

theorem thirtyoneFour_between_rpow :
    (4 : ℝ) ^ zudilinMu < 31 ∧ (31 : ℝ) < (4 : ℝ) ^ bvMu := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_between_rpow

theorem thirtyoneFour_ratio_chain :
    1 / 2 - 1 / Real.pi ^ 2 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (81 : ℝ) / 200 ∧
      (81 : ℝ) / 200 < zudilinContour := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_ratio_chain

theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu := @ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu

theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1 := @ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour

theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b := @ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion a b hb hab

theorem omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := @ErdosProblems.Erdos1049.PaperR7.omega_indicator x hx0 hx1

end PalomarCorpus.E1049.PaperStatementsC
