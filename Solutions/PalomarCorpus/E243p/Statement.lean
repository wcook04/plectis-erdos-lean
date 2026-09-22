/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243p

Every non-theorem declaration of `PalomarCorpus/E243p/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsP
open Polynomial
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η
end PalomarCorpus.E243.PaperStatementsP
