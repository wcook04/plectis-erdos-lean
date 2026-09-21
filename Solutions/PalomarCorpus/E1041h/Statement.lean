/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041h

Every non-theorem declaration of `PalomarCorpus/E1041h/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
/-- A public function spelling exactly the trinomial in both papers. Local copy of ErdosProblems.Erdos1041.PaperTrinomial.polynomialValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b
end PalomarCorpus.E1041.PaperStatementsH
