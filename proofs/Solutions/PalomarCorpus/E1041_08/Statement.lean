/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_08

Every non-theorem declaration of `PalomarCorpus/E1041_08/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open scoped ComplexConjugate

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
