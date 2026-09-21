/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band g

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

namespace PalomarCorpus.E249.PaperStatementsBG
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
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rank-one strict-subrank quotient from the first `Y` atoms. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_one_and_two :
    mobiusMersenneTheta 1 = 1 / 2 ∧
      mobiusMersenneTheta 2
        = (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.abs_mobiusMersenneTheta_sub_prefix_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) : := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_ge_alpha in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_lt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitive_form_abs_gt
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) / 480 < := by
  sorry
/-- States res:rankonefloor from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen :
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 <
      (1 : ℝ) / 15 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsBG
