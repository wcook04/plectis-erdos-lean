/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68e

Every non-theorem declaration of `PalomarCorpus/E68e/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E68.PaperStatementsE
