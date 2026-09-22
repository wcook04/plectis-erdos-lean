/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #68, band e

Erdős problem #68 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E68` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStatementsE
open scoped BigOperators
/-- Recursive lcm of a list, normalized to `1` on the empty list. Local copy of Erdos68.listLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)
/-- Product of all pairwise gcd collision terms in a list, with each unordered pair counted once. Local copy of Erdos68.pairwiseGCDProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail
/-- States long68:res:product-lcm from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  sorry
end PalomarCorpus.E68.PaperStatementsE
