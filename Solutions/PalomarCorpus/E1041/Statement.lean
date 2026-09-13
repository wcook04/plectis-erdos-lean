/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041

Every non-theorem declaration of `PalomarCorpus/E1041/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Polynomial Set
open scoped BigOperators
open Polynomial
open scoped ComplexConjugate

namespace PalomarCorpus.E1041.CriticalGeometry
open Finset
/-- The rational number 999/1000 viewed as a complex number, the common modulus of four of the five roots of the explicit quintic used for the unique-nearest-spoke obstruction. -/
noncomputable def nearestSpokeP : ℂ := (999 : ℂ) / 1000
/-- The real number (901/902) * (999/1000) = 900099/902000 viewed as a complex number, the root of index 0 in nearestSpokeRoot and the one of strictly smallest modulus among the five. -/
noncomputable def nearestSpokeA : ℂ := ((901 : ℂ) / 902) * nearestSpokeP
/-- The complex number (-451 + 780 i)/901, which has modulus exactly 1 because 451 ^ 2 + 780 ^ 2 = 901 ^ 2; it places the root of index 3 in nearestSpokeRoot on the circle of radius p. -/
noncomputable def nearestSpokeUPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901
/-- The complex conjugate (-451 - 780 i)/901 of the previous unimodular factor, placing the root of index 4 in nearestSpokeRoot on the same circle of radius p. -/
noncomputable def nearestSpokeUMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901
/-- The five roots of the explicit quintic obstruction indexed by Fin 5: the real root a = 900099/902000, the conjugate pair i p and -i p with p = 999/1000, and the conjugate pair p u₊ and p u₋ of the same modulus p. -/
noncomputable def nearestSpokeRoot : Fin 5 → ℂ
  | 0 => nearestSpokeA
  | 1 => Complex.I * nearestSpokeP
  | 2 => -Complex.I * nearestSpokeP
  | 3 => nearestSpokeP * nearestSpokeUPlus
  | 4 => nearestSpokeP * nearestSpokeUMinus
/-- The rational number 99/100 viewed as a complex number, the common modulus of the three roots of the explicit cubic used for the all-pairs midpoint obstruction. -/
noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100
/-- The primitive cube root of unity -1/2 + (√3 / 2) i, written with the real square root of 3 cast into the complex numbers. -/
noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I
/-- The three roots R, R ω and R ω ^ 2 of the explicit cubic obstruction, indexed by Fin 3, with R = 99/100 and ω the primitive cube root of unity. -/
noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2
/-- The monic cubic function z ↦ z ^ 3 - (99/100) ^ 3, whose zeros are exactly the three listed points. -/
noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3
end PalomarCorpus.E1041.CriticalGeometry

namespace PalomarCorpus.E1041.CubicPath
open Polynomial Set
open scoped BigOperators
/-- The two-segment path from a to b through the hub c, defined for every real t by c + max (1 - t) 0 * (a - c) + max (t - 1) 0 * (b - c) with the real coefficients cast into the complex numbers; it equals a at t = 0, the hub c at t = 1, and b at t = 2, and the clamped coefficients make it continuous and piecewise affine on the whole real line. -/
noncomputable def hub (a c b : ℂ) (t : ℝ) : ℂ :=
  c + ((max (1 - t) 0 : ℝ) : ℂ) * (a - c) +
    ((max (t - 1) 0 : ℝ) : ℂ) * (b - c)
end PalomarCorpus.E1041.CubicPath

namespace PalomarCorpus.E1041.CyclicTrinomialFiber
end PalomarCorpus.E1041.CyclicTrinomialFiber

namespace PalomarCorpus.E1041.FirstMergeCriticalValueSeparation
/-- The squared-length coefficient C(n, S) = (1 + S) ^ (2 / n) * log (S / (S - 1)) of the critical-value separation estimate, with the natural number n cast to a real in the exponent; the definition constrains neither n nor S. In the intended reading S is the normalised distance separating the remaining critical values from a simple saddle, and the ordinary analytic estimate of the companion paper bounds the squared length of the connector produced at that saddle by 4 * C(n, S). -/
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))
end PalomarCorpus.E1041.FirstMergeCriticalValueSeparation

namespace PalomarCorpus.E1041.QuarticQuotientFiber
end PalomarCorpus.E1041.QuarticQuotientFiber

namespace PalomarCorpus.E1041.SolvedFamilies
open Polynomial
namespace SharpCollinear
/-- The real number cos (π / (2 n)). For n ≥ 2 it is the scale that carries the two outermost zeros of the degree-n Chebyshev polynomial to -1 and 1. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp endpoint-normalised Chebyshev height C n = 1 / (2 ^ (n - 1) cos ^ n (π / (2 n))), written as the absolute value of (2 ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n. For n ≥ 2 it is the maximum modulus on [-1, 1] of the monic polynomial T n (cos (π / (2 n)) x) / (2 ^ (n - 1) cos ^ n (π / (2 n))), whose extreme zeros are -1 and 1. The exponent n - 1 is natural subtraction, and the absolute value is cosmetic because the expression is positive for every n ≥ 2; at n = 1 the inverse of cos (π / 2) is 0 by the Lean convention and the value is 0. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
end SharpCollinear
end PalomarCorpus.E1041.SolvedFamilies

namespace PalomarCorpus.E1041.TetranomialSpokes
open scoped ComplexConjugate
end PalomarCorpus.E1041.TetranomialSpokes
