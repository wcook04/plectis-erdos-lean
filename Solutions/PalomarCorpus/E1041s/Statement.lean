/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041s

Every non-theorem declaration of `PalomarCorpus/E1041s/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open Finset
open Set

namespace PalomarCorpus.E1041.PaperStatementsS
open Polynomial
open Finset
open Set
/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial `q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.chebNode, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)
/-- The sharp normalised height. A later algebraic simplification rewrites this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.comparisonBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
/-- The endpoint-normalised monic Chebyshev comparison polynomial. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹
end PalomarCorpus.E1041.PaperStatementsS
