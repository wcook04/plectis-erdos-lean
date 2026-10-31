/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.HalfGreedyFatalGap`.
-/

namespace Erdos249257.ExternalVerification257PaperStructuresH

noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)

/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by
  sorry

/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfGreedyFatalGap.two_le_of_fatal in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by
  sorry

/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresH
