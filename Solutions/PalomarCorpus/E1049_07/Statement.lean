/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_07

Every non-theorem declaration of `PalomarCorpus/E1049_07/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter

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
