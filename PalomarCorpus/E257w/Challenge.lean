/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band w

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStructuresW
open Filter
open Set
open scoped BigOperators
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- States record:257bm-c3 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_bit_stable in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_compatible_bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ} (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d := by
  sorry
end PalomarCorpus.E257.PaperStructuresW
