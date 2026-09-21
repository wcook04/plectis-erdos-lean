/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band h

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

namespace PalomarCorpus.E257.PaperStatementsAH
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
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- The first two geometric channels of the Mersenne tail. This cap is strictly weaker than the dyadic cap while still lying below the full tail. Local copy of Erdos249257.halfTwoChannelCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.halfTwoChannelCap_lt_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := by
  sorry
/-- States thm:half-skip-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosBorweinMersenneConstant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := by
  sorry
/-- States lem:gap-mass-summability from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_eq_weight_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_le_two_mul_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_lt_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.two_mul_mersenneWeight_succ_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAH
