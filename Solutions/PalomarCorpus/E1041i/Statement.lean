/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041i

Every non-theorem declaration of `PalomarCorpus/E1041i/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Polynomial

namespace PalomarCorpus.E1041.PaperStatementsI
open Set
open Polynomial
/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp normalised height. A later algebraic simplification rewrites this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.comparisonBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
end PalomarCorpus.E1041.PaperStatementsI
