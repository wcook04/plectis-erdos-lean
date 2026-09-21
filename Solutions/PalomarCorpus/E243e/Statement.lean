/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243e

Every non-theorem declaration of `PalomarCorpus/E243e/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsE
open Filter
open scoped BigOperators
/-- The correction term `Λ_n` of `long243:eq:shiftedsign`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext
end PalomarCorpus.E243.PaperStatementsE
