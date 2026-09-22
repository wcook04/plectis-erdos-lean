/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band p

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
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
/-- States catalogue:cert:d3 from the long record for Erdős problem #249. Transported from Erdos249257.linearIndependent_of_separatedMinorCertificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := by
  sorry
end PalomarCorpus.E249.PaperStructuresP
