/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band h

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsH
open scoped BigOperators
/-- States long243:res:curvature from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.cancellationFree_curvature_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cancellationFree_curvature_square
    {a aNext p pNext pNextNext q : ℤ}
    (hq : q = a * p - pNext)
    (hrec : pNextNext + a ^ 2 * p = (a + aNext) * pNext) :
    q ^ 2 + (p * pNextNext - pNext ^ 2) =
      (aNext - a) * p * pNext := by
  sorry
end PalomarCorpus.E243.PaperStatementsH
