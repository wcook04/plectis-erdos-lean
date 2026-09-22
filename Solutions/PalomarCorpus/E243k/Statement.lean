/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243k

Every non-theorem declaration of `PalomarCorpus/E243k/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E243.PaperStatementsK
/-- Numerator of the forced normalized constant-negative update. Local copy of ErdosProblems.Erdos243.forcedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forcedNumerator (n : ℕ) (a : ℤ) : ℤ :=
  (n + 1 : ℤ) * a ^ 2 - (n + 2 : ℤ) * a + (n + 3 : ℤ)
/-- Exact survival predicate for the first `remaining` forced divisions. Local copy of ErdosProblems.Erdos243.ForcedSurvives, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ForcedSurvives : ℕ → ℕ → ℤ → Prop
  | 0, _, _ => True
  | remaining + 1, index, a =>
      let d : ℤ := index + 2
      d ∣ forcedNumerator index a ∧
        ForcedSurvives remaining (index + 1)
          (forcedNumerator index a / d)
/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. Local copy of ErdosProblems.Erdos243.runningMax, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
end PalomarCorpus.E243.PaperStatementsK
