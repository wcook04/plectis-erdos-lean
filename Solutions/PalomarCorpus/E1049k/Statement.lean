/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049k

Every non-theorem declaration of `PalomarCorpus/E1049k/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsK
open scoped BigOperators
/-- Natural-valued magnitude of the forcing term in the cleared recurrence. Local copy of ErdosProblems.Erdos1049.rationalBaseForcingNat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
end PalomarCorpus.E1049.PaperStatementsK
