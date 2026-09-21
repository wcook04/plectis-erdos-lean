/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContourConstants`,
`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogConstants`,
`ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold`,
`ErdosProblems.Erdos1049.PaperOmegaIndicatorR7`,
`ErdosProblems.Erdos1049.RationalBaseContour`.
-/

namespace Erdos249257.ExternalVerification1049PaperStatementsA

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

noncomputable def paperMu : ℝ := zudilinC1 / zudilinC0

noncomputable def tailNum (x : ℝ) : ℝ :=
  2310 * x ^ 10 + 1155 * x ^ 9 + 385 * x ^ 8 - 77 * x ^ 6 + 55 * x ^ 4 - 77 * x ^ 2

noncomputable def tailHigh (x : ℝ) : ℝ := (tailNum x + 175) / (2310 * x ^ 11)

noncomputable def tailLow (x : ℝ) : ℝ := tailNum x / (2310 * x ^ 11)

noncomputable def paperBvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)

noncomputable def bvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)

noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0

noncomputable def InOmegaSupport (x : ℝ) : Prop :=
  ((1 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 12) ∨
  ((1 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 6) ∨
  ((3 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 4) ∨
  ((2 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 3) ∨
  ((5 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 5) ∨
  ((3 : ℝ) / 7 ≤ x ∧ x < (7 : ℝ) / 15) ∨
  ((1 : ℝ) / 2 ≤ x ∧ x < (8 : ℝ) / 15) ∨
  ((4 : ℝ) / 7 ≤ x ∧ x < (3 : ℝ) / 5) ∨
  ((9 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 3) ∨
  ((5 : ℝ) / 7 ≤ x ∧ x < (11 : ℝ) / 15) ∨
  ((11 : ℝ) / 14 ≤ x ∧ x < (4 : ℝ) / 5) ∨
  ((6 : ℝ) / 7 ≤ x ∧ x < (13 : ℝ) / 15) ∨
  ((13 : ℝ) / 14 ≤ x ∧ x < (14 : ℝ) / 15)

noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))

noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

/-- States long1049:res:region from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.contour_enclosure in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem contour_enclosure :
    (40568302138406054100 : ℝ) / 10 ^ 20 ≤ zudilinContour ∧
      zudilinContour ≤ (40568302138406054104 : ℝ) / 10 ^ 20 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.four_rpow_mu_lt_thirtyOne in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem four_rpow_mu_lt_thirtyOne : (4 : ℝ) ^ paperMu < 31 := by
  sorry

/-- States long1049:res:region from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_contour :
    (40568302138406054 : ℝ) / 10 ^ 17 < zudilinContour ∧
      zudilinContour < (40568302138406055 : ℝ) / 10 ^ 17 := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6 := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by
  sorry

/-- States long1049:res:region, res:rational-base-threshold from the long record and the short
record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18 := by
  sorry

/-- States long1049:res:region, res:rational-base-threshold from the long record and the short
record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu_eq in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperBvMu_eq : paperBvMu = 1 / (1 / 2 - 1 / Real.pi ^ 2) := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bvMu in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_bvMu :
    (2508284761994 : ℝ) / 10 ^ 12 < paperBvMu ∧
      paperBvMu < (2508284761995 : ℝ) / 10 ^ 12 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bv_cutoff in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_bv_cutoff :
    (3986788163576622 : ℝ) / 10 ^ 16 < 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 < (3986788163576623 : ℝ) / 10 ^ 16 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_four_rpow_bvMu in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem printed_four_rpow_bvMu :
    (32369642 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperBvMu ∧
      (4 : ℝ) ^ paperBvMu < (32369643 : ℝ) / 10 ^ 6 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_log_ratio in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_log_ratio :
    (4036981731641997 : ℝ) / 10 ^ 16 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (4036981731641998 : ℝ) / 10 ^ 16 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.inv_bvMu_eq in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem inv_bvMu_eq : 1 / bvMu = 1 / 2 - 1 / Real.pi ^ 2 := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_between_rpow in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_between_rpow :
    (4 : ℝ) ^ zudilinMu < 31 ∧ (31 : ℝ) < (4 : ℝ) ^ bvMu := by
  sorry

/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_ratio_chain in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_ratio_chain :
    1 / 2 - 1 / Real.pi ^ 2 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (81 : ℝ) / 200 ∧
      (81 : ℝ) / 200 < zudilinContour := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu := by
  sorry

/-- States res:rational-base-threshold from the short record for Erdős problem #1049.
Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1 := by
  sorry

/-- States long1049:res:region, res:rational-base-threshold from the long record and the short
record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b := by
  sorry

/-- States long1049:res:omega-indicator from the long record for Erdős problem #1049.
Transported from ErdosProblems.Erdos1049.PaperR7.omega_indicator in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStatementsA
