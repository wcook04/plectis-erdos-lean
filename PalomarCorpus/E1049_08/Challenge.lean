/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, the rational base barrier and rational base region families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.RationalBaseBarrier
open scoped BigOperators
/-- The natural number B coeff(N+1) s^(N+1): the magnitude of the forcing term that the cleared-tail recurrence leaves behind at step N, for natural data. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
/-- For a genuine rational base, meaning denominator s >= 2, together with B >= 1 and coeff(N+1) >= 1, the forcing term is at least 2^(N+1). The hypothesis s >= 2 is what separates a rational base from an integer base, where the factor s^(N+1) is 1 and the classical coordinatewise argument survives. -/
theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  sorry
end PalomarCorpus.E1049.RationalBaseBarrier

namespace PalomarCorpus.E1049.RationalBaseRegion
open scoped BigOperators
/-- The real Lambert series F(x)=sum over n at least 1 of 1/(x^n-1), with Lean tsum conventions outside its convergence domain; the irrationality theorems use x>1. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)
/-- The real series sum over k at least zero of 1/(k+x)^2, used at the positive rational arguments in the contour constant. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2
/-- The difference of two trigamma-series values used in the exact contour constant. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ :=
  trigammaSeries u - trigammaSeries v
/-- The displayed sum of thirteen trigamma differences at the rational endpoints of the Zudilin parameter intervals. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)
/-- The exact homogeneous width-rate constant 1091/2 in the constructed approximation family. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2
/-- The exact cancellation constant 266-(3/pi^2)(225-J), with J given by the thirteen displayed trigamma differences. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
/-- The exact contour C0/C1 controlling rational-base decay after homogeneous denominator clearing. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- The strict inequality log(b)/log(a)<C0/C1; the result separately requires natural a>b>0. -/
noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour
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
/-- The exact exponent bound (1-log(b)/log(a))/(C0/C1-log(b)/log(a)), with positive denominator on the strict contour region. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)
/-- For natural a>b>0 in the exact contour region, the literal Lambert value F(a/b) is irrational. The proof supplies the integer forms, positive remainder and decay internally, with no source-supply hypothesis. -/
theorem rational_base_region (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  sorry
/-- The Lambert value F(31/4) is irrational. -/
theorem thirtyone_four : Irrational (paperLambert ((31 : ℝ) / 4)) := by
  sorry
/-- On the strict contour region for natural a>b>0, bounds the irrationality exponent of F(a/b) by the displayed exact rational-base expression. -/
theorem rational_base_measure (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert ((a : ℝ) / b)) ≤
      rationalBaseMeasureBound a b := by
  sorry
/-- For every positive natural r, the irrationality exponent of F((31/4)^r) is strictly less than the paper fraction 2981509/9909. -/
theorem thirtyone_four_power_measure_lt_paper_fraction (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) <
      (2981509 : ℝ) / 9909 := by
  sorry
end PalomarCorpus.E1049.RationalBaseRegion
