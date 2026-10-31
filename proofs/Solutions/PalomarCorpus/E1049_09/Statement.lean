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

open PowerSeries
open Finset
open Filter
open scoped Topology
open scoped PowerSeries.WithPiTopology
open scoped BigOperators
open Matrix
open scoped Classical

namespace PalomarCorpus.E1049_09.Shared
/-- Local definition cK, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2
/-- Local definition gramM, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹
/-- Local definition qPochhammerFinite, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
/-- Local definition qPochhammerInfinity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
/-- Local definition actualGeneratingTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2
/-- Local definition actualGeneratingFunction, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3
end PalomarCorpus.E1049_09.Shared

namespace PalomarCorpus.E1049.PaperStructuresAA
open PowerSeries
open Finset
open Filter
open scoped Topology
open scoped PowerSeries.WithPiTopology
open scoped BigOperators
export PalomarCorpus.E1049_09.Shared (actualGeneratingFunction actualGeneratingTerm cK qPochhammerFinite qPochhammerInfinity)
/-- Local definition BW, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev BW := PowerSeries (PowerSeries ℚ)
/-- Local definition qPochhammer, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammer {R : Type*} [CommRing R] (q z : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q z n * (1 - z * q ^ n)
/-- Local definition qq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev qq : PowerSeries ℚ := PowerSeries.X
/-- Local definition qfac, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qfac (n : ℕ) : PowerSeries ℚ := qPochhammer qq qq n
/-- Local definition qPochInf, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochInf (x : BW) : BW := ∏' i : ℕ, (1 - x * C (qq ^ i))
/-- Local definition ww, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev ww : BW := PowerSeries.X
/-- Local definition momentGenFun, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def momentGenFun : BW :=
  Ring.inverse (qPochInf ww ^ 3) *
    ∑' t : ℕ, ww ^ t * C (qfac t)⁻¹ *
      (qPochInf (C (qq ^ t) * ww ^ 2) * Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2))
/-- Local definition momentWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def momentWeight (k : ℕ) : PowerSeries ℚ := coeff k momentGenFun
/-- Local definition realRogersR, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def realRogersR (r k : ℕ) (q : ℝ) : ℝ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qPochhammerFinite q q k / ∏ j, qPochhammerFinite q q (n j)
/-- Local definition gaussBinom, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0
/-- Local definition rogersPoly2, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersPoly2 (k : ℕ) : Polynomial ℤ := ∑ i ∈ range (k + 1), gaussBinom Polynomial.X k i
/-- Local definition rogersPoly3, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersPoly3 (k : ℕ) : Polynomial ℤ :=
  ∑ p ∈ antidiagonal k, ∑ q ∈ antidiagonal p.2,
    gaussBinom Polynomial.X k p.1 * gaussBinom Polynomial.X p.2 q.1
/-- Local definition rogersR, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersR (r k : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qfac k * (∏ j, qfac (n j))⁻¹
end PalomarCorpus.E1049.PaperStructuresAA

namespace PalomarCorpus.E1049.PaperStructuresAB
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology
export PalomarCorpus.E1049_09.Shared (actualGeneratingFunction actualGeneratingTerm cK gramM qPochhammerFinite qPochhammerInfinity)
/-- Local definition lambertL, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertL (q : ℝ) : ℝ := ∑' r : ℕ, q ^ (r + 1) / (1 - q ^ (r + 1))
/-- Local definition leadC, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- Local definition orderB, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def orderB (N : ℕ) : ℕ := ∑ j ∈ range N, j ^ 2
/-- Local definition sharpFactor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpFactor (q : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  qPochhammerInfinity q q ^ 4 * γ k / cK k * Real.exp (8 * lambertL q / ((k : ℝ) + 1))
/-- Local definition sharpA, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpA (q : ℝ) (γ : ℕ → ℝ) : ℝ :=
  Real.exp (-8 * Real.eulerMascheroniConstant * lambertL q) * ∏' k : ℕ, sharpFactor q γ k
/-- Local definition sharpK, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpK (q : ℝ) (γ : ℕ → ℝ) : ℝ := sharpA q γ * gramM q ^ 3
/-- Local definition actualMomentTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)
/-- Local definition actualMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t
/-- Local definition actualMomentHankel, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)
end PalomarCorpus.E1049.PaperStructuresAB

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
export PalomarCorpus.E1049_09.Shared (gramM qPochhammerInfinity)
/-- Local definition geomMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomMoment (q : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, a k * q ^ ((m + 1) * k)
/-- Local definition geomHankelDet, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomHankelDet (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin N => geomMoment q a (i.val + j.val)).det
end PalomarCorpus.E1049.PaperStructuresW
