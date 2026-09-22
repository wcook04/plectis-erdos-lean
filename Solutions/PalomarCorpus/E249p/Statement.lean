/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249p

Every non-theorem declaration of `PalomarCorpus/E249p/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Module
open Matrix

namespace PalomarCorpus.E249.PaperStructuresP
open Module
open Matrix
/-- A square nonzero evaluation minor. This is the exact finite object needed to turn number-theoretic row construction into linear independence. Local copy of Erdos249257.SeparatedMinorCertificate, restated so the compared statements elaborate against Mathlib alone. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
end PalomarCorpus.E249.PaperStructuresP
