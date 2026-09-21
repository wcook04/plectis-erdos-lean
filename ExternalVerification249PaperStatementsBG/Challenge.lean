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
`ErdosProblems.Erdos249.PaperCompleteR21.MobiusMersenneLadderLogConcavity`,
`ErdosProblems.Erdos249.RankOneSharpFloor`,
`ErdosProblems.Erdos249.RankOneSubrankObstruction`.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsBG

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mobiusMersenneTheta_one_and_two :
    mobiusMersenneTheta 1 = 1 / 2 ∧
      mobiusMersenneTheta 2
        = (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.RankOneSubrankObstruction.abs_mobiusMersenneTheta_sub_prefix_le in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) : := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_ge_alpha in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_lt_one
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem positive_direct_sum_sub_theta_two_gt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (1 : ℝ) / 480 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem primitive_form_abs_gt
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) / 480 < := by
  sorry

/-- States res:rankonefloor from the short record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen :
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 <
      (1 : ℝ) / 15 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBG
