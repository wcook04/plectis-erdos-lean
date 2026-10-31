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
`ErdosProblems.Erdos1049.IrrationalityExponentR11`,
`ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold`,
`ErdosProblems.Erdos1049.PaperLinearFormsR7`, `ErdosProblems.Erdos1049.RationalBaseContour`.
-/

open Filter
open Set
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification1049PaperStatementsI

noncomputable def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

noncomputable def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)

noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)

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

noncomputable def zudilinC1 : ℝ := 1091 / 2

noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

/-- States cor:rational-base-measure, long1049:cor:rational-base-measure from the long record
and the short record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ)) := by
  sorry

/-- States cor:rational-base-measure, long1049:cor:rational-base-measure from the long record
and the short record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301 in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 := by
  sorry

end Erdos249257.ExternalVerification1049PaperStatementsI
