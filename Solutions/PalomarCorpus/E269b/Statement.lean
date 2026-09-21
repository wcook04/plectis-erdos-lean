/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269b

Every non-theorem declaration of `PalomarCorpus/E269b/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E269.PaperStatementsB
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹
/-- Canonical positive representative of an integer modulo `C`: a zero residue is represented by `C`, and every nonzero residue by its nonnegative Euclidean remainder. The definition is total at `C = 0`, but all theorems using its positive-representative meaning assume `0 < C`. Local copy of ErdosProblems.Erdos269.leastPositiveResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
end PalomarCorpus.E269.PaperStatementsB
