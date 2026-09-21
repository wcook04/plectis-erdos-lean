/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band s

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStatementsAS
open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- An exact finite Boolean quotient row at endpoint `n`. Local copy of Erdos249257.ExactLocalMersenneHalfRow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Weighted sum of a Boolean word. The equal-length hypotheses below make the two fallback equations irrelevant. Local copy of Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- The binary-boundary target before any selected divisor weights are removed. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The weights with indices `d,d+1,…,s-1`, in descending size order. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The actual proper-divisor weight word, indexed by `2,…,s-1`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- Integer seam remainder normalized by the row-square scale. Local copy of Erdos249257.seamGreedyNormalizedRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyNormalizedRemainder (s : ℕ) : ℝ :=
  (seamIntegerGreedyRemainder s : ℝ) / (4 : ℝ) ^ s
/-- A cofinal row sequence along which the normalized seam remainder vanishes. This is strictly weaker than a uniform exponential bound. Local copy of Erdos249257.SeamGreedyRemainderSubquadraticAlong, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SeamGreedyRemainderSubquadraticAlong (rows : ℕ → ℕ) : Prop :=
  Tendsto rows atTop atTop ∧
    Tendsto (fun j => seamGreedyNormalizedRemainder (rows j))
      atTop (nhds 0)
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The natural exponent support encoded by a finite seam word. Local copy of Erdos249257.seamWordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- The real achievement-set point coded by the integer-greedy seam word. Local copy of Erdos249257.seamGreedyFiniteValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyFiniteValue (s : ℕ) : ℝ :=
  positiveMersenneSupportValue
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)
/-- `X_G(2)`: the value of the real greedy support for the half target. Definition taken from `PaperCompleteR21/SeamQuotientDeficitLimit.lean`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.greedyHalfTargetValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfTargetValue : ℝ :=
  positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ))
/-- The paper's `δ = 1/2 - X_G(2)`. Taken from `PaperCompleteR21/SeamQuotientDeficitLimit.lean`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.seamGreedyLimitDeficit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyLimitDeficit : ℝ := 1 / 2 - greedyHalfTargetValue
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_limit_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_seam_limit_unconditional :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) ∧
      Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) ∧
      seamGreedyLimitDeficit = 1 / 2 - greedyHalfTargetValue ∧
      0 ≤ seamGreedyLimitDeficit ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        Tendsto seamGreedyNormalizedRemainder atTop (nhds 0)) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows) := by
  sorry
/-- States record:257bm-i6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharper_additive_estimate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card := by
  sorry
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
/-- States record:257bm-i6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2 := by
  sorry
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyFiniteValue_greedyHalfTargetValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_seamGreedyFiniteValue_greedyHalfTargetValue :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) := by
  sorry
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyNormalizedRemainder in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_seamGreedyNormalizedRemainder :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAS
