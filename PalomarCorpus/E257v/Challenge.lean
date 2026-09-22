/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band v

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresV
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe_actualTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unitNumerator_skipSafe_actualTail {k u L a : ℕ}
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k := by
  sorry
end PalomarCorpus.E257.PaperStructuresV
