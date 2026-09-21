/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band k

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset

namespace PalomarCorpus.E249.PaperStatementsBK
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound : := by
  sorry
end PalomarCorpus.E249.PaperStatementsBK
