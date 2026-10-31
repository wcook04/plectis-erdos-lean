/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_01

Every non-theorem declaration of `PalomarCorpus/E1049_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1049.PaperStatementsA

namespace PalomarCorpus.E1049.PaperStatementsJ
open Filter
open scoped Topology
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (paperLambert trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm zudilinMu)
end PalomarCorpus.E1049.PaperStatementsJ

namespace PalomarCorpus.E1049.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
/-- The height region in the Bundschuh--Väänänen theorem, written in the form needed for a positive reduced rational base `a / b`. This definition records only the elementary parameter inequality; it does not internalize the external analytic irrationality theorem. Local copy of ErdosProblems.Erdos1049.BundschuhVaananenHeightRegion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
end PalomarCorpus.E1049.PaperStatementsG

namespace PalomarCorpus.E1049.PaperStatementsI
open Filter
open Set
open scoped BigOperators
open scoped Topology
export PalomarCorpus.E1049_01.Shared (approximationExponents irrationalityExponent paperLambert reducedApproximationPairs trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
end PalomarCorpus.E1049.PaperStatementsI

namespace PalomarCorpus.E1049.RationalBaseRegion
open scoped BigOperators
export PalomarCorpus.E1049_01.Shared (ZudilinContourRegion approximationExponents irrationalityExponent paperLambert reducedApproximationPairs trigammaSeries zudilinC0 zudilinC1 zudilinContour zudilinJ zudilinJTerm)
/-- The exact exponent bound (1-log(b)/log(a))/(C0/C1-log(b)/log(a)), with positive denominator on the strict contour region. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)
end PalomarCorpus.E1049.RationalBaseRegion
