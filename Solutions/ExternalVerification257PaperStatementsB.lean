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

namespace Erdos249257.ExternalVerification257PaperStatementsB

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

noncomputable def greedyMersenneSecondChannelPhaseRat (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n *
    (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n
      - ((1 : ℚ) / 2) ^ n)

noncomputable def HalfSecondChannelSeparatedRat (n : ℕ) : Prop :=
  (1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n
    ≤ |greedyMersenneSecondChannelPhaseRat n - 1 / 3|

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSecondChannelPhase (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n *
    (2 * greedyMersenneRemainder (1 / 2 : ℝ) n
      - ((1 : ℝ) / 2) ^ n)

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n

noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  set_option smartUnfolding false in
  exact @Erdos249257.greedy_survives_of_mem_mersenneAchievementSet x hx

theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite

theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation hseparate

theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven hseparate

theorem half_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfDyadicCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap hskip

theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap hskip

theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival x

theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite x hx hskips

theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.mem_mersenneAchievementSet_of_greedy_survival x hx hsurvive

end Erdos249257.ExternalVerification257PaperStatementsB
