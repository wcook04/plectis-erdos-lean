/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band o

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace PalomarCorpus.E249.PaperStatementsO
open scoped BigOperators
open Matrix
open ArithmeticFunction
/-- The `n`th atom of the Möbius--Mersenne power ladder, with the positive integer index shifted to `n + 1`. Local copy of Erdos249257.SignedQMomentObstruction.mobiusMersenneTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The Möbius--Mersenne power ladder `Θᵣ`. Local copy of Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The `n`th atom of the Möbius--Mersenne power ladder, with the positive integer index shifted to `n + 1`. Local copy of Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SignedQMomentObstruction_mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, SignedQMomentObstruction_mobiusMersenneTerm r n
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersennePrefix_eq_icc_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.rankOne_denominator_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsO
