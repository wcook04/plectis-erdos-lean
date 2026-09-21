/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243d

Every non-theorem declaration of `PalomarCorpus/E243d/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243.PaperStatementsD
open Filter
open scoped BigOperators
open scoped Topology
/-- `ℓ x = log₂ log₂ max(4, x)`, the scale of the long #243 note. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.ellScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ellScale (x : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (max 4 x))
end PalomarCorpus.E243.PaperStatementsD
