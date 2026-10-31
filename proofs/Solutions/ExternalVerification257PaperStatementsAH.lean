/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GreedyAchievementSet

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GreedyAchievementSet`.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAH

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n

noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n

theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := @Erdos249257.halfTwoChannelCap_lt_mersenneTail n

theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := @Erdos249257.irrational_erdosBorweinMersenneConstant

theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n := @Erdos249257.mersenneGap_pos n hn

theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := @Erdos249257.mersenneTail_eq_weight_add n

theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := @Erdos249257.mersenneTail_le_two_mul_weight n

theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := @Erdos249257.mersenneTail_lt_weight n hn

theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := @Erdos249257.two_mul_mersenneWeight_succ_lt n hn

end Erdos249257.ExternalVerification257PaperStatementsAH
