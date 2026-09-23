/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_08

Every non-theorem declaration of `PalomarCorpus/E1049_08/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter
open Finset
open Topology
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace PalomarCorpus.E1049_08.Shared
/-- Local definition leadC, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- Local definition qPochhammerFinite, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
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
/-- Local definition qPochhammerInfinity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
end PalomarCorpus.E1049_08.Shared

namespace PalomarCorpus.E1049.ArchimedeanCap
open Filter Asymptotics
open scoped Topology
/-- The declared clearing width of the n-th approximation pair: the larger of the degrees of the polynomials U n and V n, as a natural number. Under the Mathlib convention the zero polynomial has degree zero. -/
noncomputable def width (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ := max (U n).natDegree (V n).natDegree
/-- The l^1 coefficient norm of an integer polynomial, the sum over its support of the absolute values of its coefficients, returned as a real number; the zero polynomial has empty support and height 0. -/
noncomputable def height (P : Polynomial ℤ) : ℝ := ∑ i ∈ P.support, |(P.coeff i : ℝ)|
/-- The remainder U_n(x) F(x) - V_n(x) of the n-th pair at the real point x, the polynomials being evaluated through the canonical ring map from the integers to the reals. Here F is an arbitrary real function supplied as a parameter rather than a fixed Lambert series. -/
noncomputable def remainder (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x - (V n).eval₂ (Int.castRingHom ℝ) x
end PalomarCorpus.E1049.ArchimedeanCap

namespace PalomarCorpus.E1049.BezoutPluckerJets
open scoped BigOperators
end PalomarCorpus.E1049.BezoutPluckerJets

namespace PalomarCorpus.E1049.HermitePadeNoGo
/-- The decay exponent (1 + rho^2)/2 + sigma of that model: the normalised rate at which the remainder of the two-function approximation shrinks, in the two real parameters rho and sigma. Reading rho as the rectangularity parameter of the multi-index and sigma as the degree parameter is an interpretation; the statements below use only the formula and the admissible region rho >= 0, sigma >= 1 + rho. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- The height exponent (1 + rho)^2/2 + sigma (1 + rho) of that model: the normalised logarithmic cost of clearing denominators, at the same parameters rho and sigma. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- The cyclotomic saving exponent 3 sigma^2 / pi^2 of the rectangular two-function Hermite-Pade exponent model: the normalised logarithmic size of the common cyclotomic factor removable from a pair of approximation polynomials at model parameter sigma, the constant 3/pi^2 being the mean density in the summatory totient estimate. Reading sigma as a degree parameter is an interpretation, and no statement here uses it. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- Rational-base height threshold associated with the explicit exponent model above. Local copy of ErdosProblems.Erdos1049.hpThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
/-- The denominator-cleared comparison functional (pi^2 + 2) hpDecay - 6 sigma^2 - (pi^2 - 2) hpHeight, whose sign decides whether the rectangular two-function threshold of the model exceeds the classical one-function threshold 1/2 - 1/pi^2. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma
end PalomarCorpus.E1049.HermitePadeNoGo

namespace PalomarCorpus.E1049.PaperStatementsU
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology
export PalomarCorpus.E1049_08.Shared (actualMoment actualMomentHankel actualMomentTerm leadC qPochhammerFinite qPochhammerInfinity)
/-- Local definition lambertTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)
/-- Local definition lambert, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n
end PalomarCorpus.E1049.PaperStatementsU

namespace PalomarCorpus.E1049.PaperStructuresAB
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology
export PalomarCorpus.E1049_08.Shared (actualMoment actualMomentHankel actualMomentTerm leadC qPochhammerFinite qPochhammerInfinity)
/-- Local definition gramM, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹
/-- Local definition cK, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2
/-- Local definition lambertL, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertL (q : ℝ) : ℝ := ∑' r : ℕ, q ^ (r + 1) / (1 - q ^ (r + 1))
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
/-- Local definition actualGeneratingTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2
/-- Local definition actualGeneratingFunction, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3
end PalomarCorpus.E1049.PaperStructuresAB
