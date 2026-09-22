/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #68d

Independent Comparator restatement of the paper-linked Lean that actually has
Comparator-grade proof coverage for this problem. Parent problem remains open.
Narrative lives in `PalomarCorpus/README.md`.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStructuresD
open scoped BigOperators
noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)

noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail

theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  sorry

end PalomarCorpus.E68.PaperStructuresD
