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
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- Exact rational version of the greedy residual. Local copy of Erdos249257.greedyMersenneRemainderRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- Rational form of the second-channel phase. Its branch arithmetic can be proved over `ℚ` and then transferred to the real coordinate below. Local copy of Erdos249257.greedyMersenneSecondChannelPhaseRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSecondChannelPhaseRat (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n *
    (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n
      - ((1 : ℚ) / 2) ^ n)
/-- Decidable rational form of the shrinking-hole avoidance condition. Local copy of Erdos249257.HalfSecondChannelSeparatedRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfSecondChannelSeparatedRat (n : ℕ) : Prop :=
  (1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n
    ≤ |greedyMersenneSecondChannelPhaseRat n - 1 / 3|
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The normalized phase at the first scale where the second geometric channel of the Mersenne tail is visible. Local copy of Erdos249257.greedyMersenneSecondChannelPhase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSecondChannelPhase (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n *
    (2 * greedyMersenneRemainder (1 / 2 : ℝ) n
      - ((1 : ℝ) / 2) ^ n)
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- The first two geometric channels of the Mersenne tail. This cap is strictly weaker than the dyadic cap while still lying below the full tail. Local copy of Erdos249257.halfTwoChannelCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- States thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.greedy_survives_of_mem_mersenneAchievementSet in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.halfTwoChannelCap_lt_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := by
  sorry
/-- States record:257bm-c20, thm:half-skip-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  sorry
/-- States thm:second-channel from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:second-channel from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:two-channel-cap from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfDyadicCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:two-channel-cap from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:half-skip-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosBorweinMersenneConstant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := by
  sorry
/-- States thm:greedy-survival-catalogue, thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  sorry
/-- States record:257bm-c20 from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet := by
  sorry
/-- States thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_of_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
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
