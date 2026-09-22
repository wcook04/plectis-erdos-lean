/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.SignedQMomentObstruction`,
`Erdos257PeriodNoncollapse.SignedQMomentObstruction`,
`ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits`,
`ErdosProblems.Erdos249.PaperCompleteR7.ShortNoteAssemblies`,
`ErdosProblems.Erdos249.RankOneSubrankObstruction`.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsO

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def SignedQMomentObstruction_mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, SignedQMomentObstruction_mobiusMersenneTerm r n

/-- States prop:b6 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersennePrefix_eq_icc_sum in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r := by
  sorry

/-- States prop:b6 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR7.rankOne_denominator_pos in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsO
