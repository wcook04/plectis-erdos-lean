/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band c

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E1049.PaperStatementsC
/-- `C₁ = (α₀+α₁+α₂)β - (α₁²+α₂²+β²)/2 = 1091/2`, Zudilin's (25). Local copy of ErdosProblems.Erdos1049.zudilinC1, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2
/-- The series representation of the trigamma function. Only this series is used; the identification with `d²/dx² log Γ` is classical and not needed. Local copy of ErdosProblems.Erdos1049.trigammaSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2
/-- One interval's contribution `ψ₁(u) - ψ₁(v)`. Local copy of ErdosProblems.Erdos1049.zudilinJTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v
/-- `J = ∫₀¹ ω(x) d(-ψ'(x))` over the thirteen intervals on which `ω = 1` (Zudilin 2004, end of Section 5), written as the trigamma series. Local copy of ErdosProblems.Erdos1049.zudilinJ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)
/-- `C₀ = α₁²/2 + α₀α₁ + (β-α₂)(α₂-α₁) - (3/π²)(m² - J)` with `m = 15`, Zudilin's (26). Local copy of ErdosProblems.Erdos1049.zudilinC0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
/-- `μ = C₁/C₀`, the irrationality-exponent constant printed in the theorem. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.paperMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperMu : ℝ := zudilinC1 / zudilinC0
/-- Numerator of the Euler–Maclaurin tail over `2310 x¹¹`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailNum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailNum (x : ℝ) : ℝ :=
  2310 * x ^ 10 + 1155 * x ^ 9 + 385 * x ^ 8 - 77 * x ^ 6 + 55 * x ^ 4 - 77 * x ^ 2
/-- `tailLow x + 5/(66x¹¹)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailHigh, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailHigh (x : ℝ) : ℝ := (tailNum x + 175) / (2310 * x ^ 11)
/-- `1/x + 1/(2x²) + 1/(6x³) - 1/(30x⁵) + 1/(42x⁷) - 1/(30x⁹)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailLow (x : ℝ) : ℝ := tailNum x / (2310 * x ^ 11)
/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh–Väänänen exponent. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperBvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)
/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh–Väänänen exponent. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.bvMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)
/-- `μ = C₁/C₀`, the reciprocal of the contour `θ* = C₀/C₁`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0
/-- Exactly the thirteen half-open intervals printed in the long record. Local copy of ErdosProblems.Erdos1049.PaperR7.InOmegaSupport, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- Local copy of ErdosProblems.Erdos1049.PaperR7.omegaWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))
/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the irrationality-exponent bound of Zudilin's Theorem 1. Local copy of ErdosProblems.Erdos1049.zudilinContour, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- The parameter region of the authored rational-base theorem: reduced bases `a/b` with `log b / log a < θ*`. Membership is the hypothesis the ordinary proof consumes; it is not an irrationality statement. Local copy of ErdosProblems.Erdos1049.ZudilinContourRegion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour
/-- States long1049:res:region from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.contour_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem contour_enclosure :
    (40568302138406054100 : ℝ) / 10 ^ 20 ≤ zudilinContour ∧
      zudilinContour ≤ (40568302138406054104 : ℝ) / 10 ^ 20 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.four_rpow_mu_lt_thirtyOne in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_rpow_mu_lt_thirtyOne : (4 : ℝ) ^ paperMu < 31 := by
  sorry
/-- States long1049:res:region from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_contour :
    (40568302138406054 : ℝ) / 10 ^ 17 < zudilinContour ∧
      zudilinContour < (40568302138406055 : ℝ) / 10 ^ 17 := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6 := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by
  sorry
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18 := by
  sorry
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperBvMu_eq : paperBvMu = 1 / (1 / 2 - 1 / Real.pi ^ 2) := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bvMu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_bvMu :
    (2508284761994 : ℝ) / 10 ^ 12 < paperBvMu ∧
      paperBvMu < (2508284761995 : ℝ) / 10 ^ 12 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bv_cutoff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_bv_cutoff :
    (3986788163576622 : ℝ) / 10 ^ 16 < 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 < (3986788163576623 : ℝ) / 10 ^ 16 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_four_rpow_bvMu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_four_rpow_bvMu :
    (32369642 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperBvMu ∧
      (4 : ℝ) ^ paperBvMu < (32369643 : ℝ) / 10 ^ 6 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_log_ratio in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_log_ratio :
    (4036981731641997 : ℝ) / 10 ^ 16 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (4036981731641998 : ℝ) / 10 ^ 16 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.inv_bvMu_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem inv_bvMu_eq : 1 / bvMu = 1 / 2 - 1 / Real.pi ^ 2 := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_between_rpow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_between_rpow :
    (4 : ℝ) ^ zudilinMu < 31 ∧ (31 : ℝ) < (4 : ℝ) ^ bvMu := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_ratio_chain in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_ratio_chain :
    1 / 2 - 1 / Real.pi ^ 2 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (81 : ℝ) / 200 ∧
      (81 : ℝ) / 200 < zudilinContour := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1 := by
  sorry
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b := by
  sorry
/-- States long1049:res:omega-indicator from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.omega_indicator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsC
