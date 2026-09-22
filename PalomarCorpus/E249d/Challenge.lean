/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band d

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set

namespace PalomarCorpus.E249.PaperStatementsD
open Filter
open Set
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := by
  sorry
end PalomarCorpus.E249.PaperStatementsD
