/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_03

Every non-theorem declaration of `PalomarCorpus/E1041_03/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Polynomial
open Finset
open scoped NNReal
open scoped ENNReal

namespace PalomarCorpus.E1041_03.Shared
/-- The real number cos (π / (2 n)). For n ≥ 2 it is the scale that carries the two outermost zeros of the degree-n Chebyshev polynomial to -1 and 1. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp endpoint-normalised Chebyshev height C n = 1 / (2 ^ (n - 1) cos ^ n (π / (2 n))), written as the absolute value of (2 ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n. For n ≥ 2 it is the maximum modulus on [-1, 1] of the monic polynomial T n (cos (π / (2 n)) x) / (2 ^ (n - 1) cos ^ n (π / (2 n))), whose extreme zeros are -1 and 1. The exponent n - 1 is natural subtraction, and the absolute value is cosmetic because the expression is positive for every n ≥ 2; at n = 1 the inverse of cos (π / 2) is 0 by the Lean convention and the value is 0. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
end PalomarCorpus.E1041_03.Shared

namespace PalomarCorpus.E1041.PaperStatementsI
open Set
open Polynomial
export PalomarCorpus.E1041_03.Shared (comparisonBound endpointScale)
end PalomarCorpus.E1041.PaperStatementsI

namespace PalomarCorpus.E1041.PaperStatementsE
open Polynomial
open Finset
open Set
/-- The conclusion of the sharp collinear diameter theorem, with the constant left as a parameter `K`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CollinearDiameterBound (n : ℕ) (K : ℝ) : Prop :=
  ∀ base dir : ℂ, ‖dir‖ = 1 → ∀ (y : Fin n → ℝ) (f : ℂ[X]),
    f = (∏ k, (X - C (base + dir * (y k : ℂ)))) → ∀ D : ℝ,
      IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ K * (D / 2) ^ n
end PalomarCorpus.E1041.PaperStatementsE

namespace PalomarCorpus.E1041.PaperStatementsS
open Polynomial
open Finset
open Set
export PalomarCorpus.E1041_03.Shared (comparisonBound endpointScale)
/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial `q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.chebNode, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)
/-- The endpoint-normalised monic Chebyshev comparison polynomial. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹
end PalomarCorpus.E1041.PaperStatementsS

namespace PalomarCorpus.E1041.PaperStatementsT
open Polynomial
open Finset
open Set
open scoped NNReal
open scoped ENNReal
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
end PalomarCorpus.E1041.PaperStatementsT
