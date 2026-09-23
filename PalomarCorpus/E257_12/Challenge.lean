/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.1: conditional membership tests (part 3 of 6)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped BigOperators
open scoped ENNReal
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257_12.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257_12.Shared

namespace PalomarCorpus.E257.PaperStructuresBV
open Filter
open scoped BigOperators
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The list of truncated Mersenne weights at seam row s for the ranks from the given starting index up to s minus 1, in increasing rank order. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The seam weight list at row s, namely the truncated Mersenne weights for ranks 2 up to s minus 1. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local definition listGreedyRemAfter, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def listGreedyRemAfter : ℕ → List ℕ → ℕ → ℕ
  | 0, _, C => C
  | _ + 1, [], C => C
  | m + 1, w :: ws, C => listGreedyRemAfter m ws (if w ≤ C then C - w else C)
/-- Local definition seamIntRem, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamIntRem (s m : ℕ) : ℕ :=
  listGreedyRemAfter m (seamWeights s) (seamSubsetTarget s)
/-- Local definition seamScaledTarget, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamScaledTarget (s : ℕ) : ℝ :=
  (seamSubsetTarget s : ℝ) / (4 : ℝ) ^ s
/-- Local definition seamScaledWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamScaledWeight (s d : ℕ) : ℝ :=
  (truncatedMersenneWeight s d : ℝ) / (4 : ℝ) ^ s
/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight system `v`, in increasing order of rank, starting at rank `2`. `tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
  sorry
end PalomarCorpus.E257.PaperStructuresBV

namespace PalomarCorpus.E257.PaperStatementsB
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_12.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
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
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- The first two geometric channels of the Mersenne tail. This cap is strictly weaker than the dyadic cap while still lying below the full tail. Local copy of Erdos249257.halfTwoChannelCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
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
end PalomarCorpus.E257.PaperStatementsB

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_12.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet := by
  sorry
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM
