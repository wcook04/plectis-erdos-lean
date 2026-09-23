/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_09

Every non-theorem declaration of `PalomarCorpus/E1049_09/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Filter
open Matrix
open scoped Topology
open scoped BigOperators
open scoped Classical

namespace PalomarCorpus.E1049.PaperStructuresV
open Finset
/-- Local definition rowModD, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rowModD (D : ℕ) (v : ℤ × ℤ) : ZMod D × ZMod D := ((v.1 : ZMod D), (v.2 : ZMod D))
/-- Local definition tailPartialSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailPartialSum (a b m : ℕ) : ℚ :=
  ∑ r ∈ Icc 1 m, ((b : ℚ) / a) ^ r / (1 - ((b : ℚ) / a) ^ r)
/-- Local definition tailP, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailP (a b m : ℕ) : ℤ := (tailPartialSum a b m).num
/-- Local definition tailQ, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailQ (a b m : ℕ) : ℤ := ((tailPartialSum a b m).den : ℤ)
/-- Local definition tailMinor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailMinor (a b i j : ℕ) : ℤ := tailQ a b i * tailP a b j - tailP a b i * tailQ a b j
/-- Local definition tailRow, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailRow (a b m : ℕ) : ℤ × ℤ := (tailQ a b m, tailP a b m)
/-- Local definition tailPrefixLattice, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailPrefixLattice (a b M : ℕ) : Submodule ℤ (ℤ × ℤ) :=
  Submodule.span ℤ (tailRow a b '' Set.Iio M)
end PalomarCorpus.E1049.PaperStructuresV

namespace PalomarCorpus.E1049.PaperStructuresW
open Filter
open Finset
open Matrix
open scoped Topology
open scoped BigOperators
open scoped Classical
/-- Local definition geomMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomMoment (q : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, a k * q ^ ((m + 1) * k)
/-- Local definition geomHankelDet, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomHankelDet (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin N => geomMoment q a (i.val + j.val)).det
/-- Local definition gramM, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹
/-- Local definition qPochhammerInfinity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
end PalomarCorpus.E1049.PaperStructuresW

namespace PalomarCorpus.E1049.PrimeSupportSelectors
open Filter
end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions
/-- The parameter region log b / log a < 1/2 - 1/pi^2 of the published Bundschuh-Vaananen criterion, written for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This records only the elementary parameter inequality; their analytic irrationality theorem is not internalised, so membership is applicability of a method rather than an irrationality statement. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- The parameter region log b / log a < 81/200 for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This threshold is defined here as an elementary sub-boundary of the region reached by the project's separate ordinary rational-base theorem; it is not a published criterion and carries no analytic hypothesis. -/
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
end PalomarCorpus.E1049.PublishedHeightRegions

namespace PalomarCorpus.E1049.RationalBaseBarrier
open scoped BigOperators
/-- The natural number B coeff(N+1) s^(N+1): the magnitude of the forcing term that the cleared-tail recurrence leaves behind at step N, for natural data. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
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
end PalomarCorpus.E1049.RationalBaseRegion
