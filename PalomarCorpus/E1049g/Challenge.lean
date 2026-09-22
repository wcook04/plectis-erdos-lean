/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band g

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsG
open scoped BigOperators
/-- The height region in the Bundschuh--Väänänen theorem, written in the form needed for a positive reduced rational base `a / b`. This definition records only the elementary parameter inequality; it does not internalize the external analytic irrationality theorem. Local copy of ErdosProblems.Erdos1049.BundschuhVaananenHeightRegion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
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
/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the irrationality-exponent bound of Zudilin's Theorem 1. Local copy of ErdosProblems.Erdos1049.zudilinContour, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- The parameter region of the authored rational-base theorem: reduced bases `a/b` with `log b / log a < θ*`. Membership is the hypothesis the ordinary proof consumes; it is not an irrationality statement. Local copy of ErdosProblems.Erdos1049.ZudilinContourRegion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour
/-- Hankel matrix of an arbitrary power-series moment sequence. Local copy of ErdosProblems.Erdos1049.zudilinMomentMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))
/-- Finite `q`-Pochhammer product `(q^start;q)_len`, represented as an integer formal power series. Local copy of ErdosProblems.Erdos1049.zudilinPochhammerPS, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)
/-- The unit factor in the `t`th normalized summand `(q;q)_n^3(q^(t+1);q)_n/(q^(n+1+t);q)_(n+1)`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedTailUnit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1
/-- The exact `t`th summand of Zudilin's normalized moment `v_n^*` at `x=z=1`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t
/-- Zudilin's normalized moment `v_n^*` as a genuine formal power series. For each coefficient `q^d`, only tails `t≤d/(n+1)` can contribute, so the source infinite sum is defined coefficientwise by this exact finite sum. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)
/-- Zudilin's normalized Hankel determinant `V_N^*`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedHankelDet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det
/-- States long1049:res:31over4 from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4 := by
  sorry
/-- States long1049:res:zudilin-sharp-qorder, res:zudilin-sharp-qorder from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsG
