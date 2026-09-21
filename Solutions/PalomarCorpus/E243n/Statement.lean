/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243n

Every non-theorem declaration of `PalomarCorpus/E243n/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Finset

namespace PalomarCorpus.E243.PaperStatementsN
open Filter
open Finset
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.cubicRatioError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))
/-- The rising cubic used in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR20.risingCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)
end PalomarCorpus.E243.PaperStatementsN
