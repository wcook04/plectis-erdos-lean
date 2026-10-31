/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, record section 2: the region b^ mu < a and the base 31/4; positive linear forms with integer coefficients

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open Filter
open scoped Topology
open scoped BigOperators
open Set

namespace PalomarCorpus.E1049_01.Shared
/-- The real Lambert series F(x)=sum over n at least 1 of 1/(x^n-1), with Lean tsum conventions outside its convergence domain; the irrationality theorems use x>1. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)
/-- Reduced integer-numerator, positive-natural-denominator rational approximants to xi with error strictly below q^(-nu). -/
noncomputable def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}
/-- The real exponents admitting infinitely many reduced rational approximants at the stated strict error bound. -/
noncomputable def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}
/-- The supremum of approximation exponents for the real target; the theorem applies it to the irrational Lambert values supplied by the same construction. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)
/-- The real series sum over k at least zero of 1/(k+x)^2, used at the positive rational arguments in the contour constant. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2
/-- The exact homogeneous width-rate constant 1091/2 in the constructed approximation family. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2
/-- The difference of two trigamma-series values used in the exact contour constant. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v
/-- The displayed sum of thirteen trigamma differences at the rational endpoints of the Zudilin parameter intervals. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)
/-- The exact cancellation constant 266-(3/pi^2)(225-J), with J given by the thirteen displayed trigamma differences. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
/-- The exact contour C0/C1 controlling rational-base decay after homogeneous denominator clearing. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- The strict inequality log(b)/log(a)<C0/C1; the result separately requires natural a>b>0. -/
noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour
/-- `μ = C₁/C₀`, the reciprocal of the contour `θ* = C₀/C₁`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0
end PalomarCorpus.E1049_01.Shared

namespace PalomarCorpus.E1049.PaperStatementsA
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm zudilinMu)
/-- `μ = C₁/C₀`, the irrationality-exponent constant printed in the theorem. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.paperMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperMu : ℝ := zudilinC1 / zudilinC0
/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh-Väänänen exponent. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperBvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)
/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh-Väänänen exponent. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.bvMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)
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
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6 := by
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
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b := by
  sorry
/-- States long1049:res:omega-indicator from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.omega_indicator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsA

namespace PalomarCorpus.E1049.PaperStatementsJ
open Filter
open scoped Topology
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (paperLambert trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm zudilinMu)
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  sorry
/-- States long1049:res:region, res:rational-base-threshold from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_irrational : Irrational (paperLambert ((31 : ℝ) / 4)) := by
  sorry
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_pow_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_pow_irrational (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsJ

namespace PalomarCorpus.E1049.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
/-- The height region in the Bundschuh--Väänänen theorem, written in the form needed for a positive reduced rational base `a / b`. This definition records only the elementary parameter inequality; it does not internalize the external analytic irrationality theorem. Local copy of ErdosProblems.Erdos1049.BundschuhVaananenHeightRegion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4 := by
  sorry
end PalomarCorpus.E1049.PaperStatementsG

namespace PalomarCorpus.E1049.PaperStatementsI
open Filter
open Set
open scoped BigOperators
open scoped Topology
export PalomarCorpus.E1049_01.Shared (approximationExponents irrationalityExponent paperLambert reducedApproximationPairs trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
/-- States cor:rational-base-measure, long1049:cor:rational-base-measure from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ)) := by
  sorry
/-- States cor:rational-base-measure, long1049:cor:rational-base-measure from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 := by
  sorry
end PalomarCorpus.E1049.PaperStatementsI

namespace PalomarCorpus.E1049.RationalBaseRegion
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion approximationExponents irrationalityExponent paperLambert reducedApproximationPairs trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
/-- The exact exponent bound (1-log(b)/log(a))/(C0/C1-log(b)/log(a)), with positive denominator on the strict contour region. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)
/-- The same irrationality-exponent bound holds uniformly for F((a/b)^r) at every positive natural power r of a base in the strict contour region. -/
theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b := by
  sorry
/-- For every positive natural r, the irrationality exponent of F((31/4)^r) is strictly less than 301. -/
theorem thirtyone_four_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 := by
  sorry
end PalomarCorpus.E1049.RationalBaseRegion
