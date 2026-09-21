/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243g

Every non-theorem declaration of `PalomarCorpus/E243g/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Finset

namespace PalomarCorpus.E243.PaperStatementsG
open Filter
open Finset
/-- The literal error in `C (n+1) / C n = 1 + l/n + ε_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.rateError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rateError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C (n + 1) / C n - (1 + l / (n : ℝ))
/-- `risingPow d x = x (x+1) ⋯ (x + d - 1)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.risingPow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingPow (d : ℕ) (x : ℝ) : ℝ := ∏ i ∈ Finset.range d, (x + (i : ℝ))
end PalomarCorpus.E243.PaperStatementsG
