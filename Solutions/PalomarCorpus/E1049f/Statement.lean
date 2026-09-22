/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049f

Every non-theorem declaration of `PalomarCorpus/E1049f/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial

namespace PalomarCorpus.E1049.PaperStatementsF
open Polynomial
/-- Integer homogeneous evaluation of an integral polynomial at `(3,2)`, using the declared ambient width `W`. Local copy of ErdosProblems.Erdos1049.homEvalThreeTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
/-- The bottom `3`-adic endpoint jet of depth `R`. Local copy of ErdosProblems.Erdos1049.bottomJet3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
/-- Integer homogeneous evaluation at a reduced numerator--denominator pair. The existing `homEvalThreeTwo` is the specialization `(a,b) = (3,2)`. This generic form is the arithmetic object used in Proposition 3.6 of the paper. Local copy of ErdosProblems.Erdos1049.homEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEval (a b W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * a ^ i * b ^ (W - i)
end PalomarCorpus.E1049.PaperStatementsF
