/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.1: conditional membership tests (part 4 of 5)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Set
open scoped BigOperators
open Filter
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257_13.Shared
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The remainder left by the greedy Mersenne rule applied to a nonnegative real x through rank n: it starts at x and, at each rank n+1, subtracts the weight 1 divided by 2 to the power n+1 minus 1 exactly when that weight is at most the current remainder. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The rational greedy Mersenne remainder of a rational target x through rank n, computed exactly in the rationals: it starts at x and at each rank n+1 subtracts the rational weight 1 divided by 2 to the power n+1 minus 1 exactly when that weight is at most the current remainder. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- Integer numerator of the frozen coefficient window. The recurrence uses the binary weights `2^(J-i)` without division. Local copy of Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J` future divisor-incidence rows cover the centered carry at depth `k`. Local copy of Erdos249257.greedyHalfFrozenMargin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k
/-- Direct full-shell sign socket. It asks only that the actual frozen margin has already crossed by the full-shell horizon at every genuine skipped rank; no seam or abstract adjacent-cut coordinate remains in the hypothesis. Local copy of Erdos249257.HalfGreedySkippedFullShellNonnegative, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n
end PalomarCorpus.E257_13.Shared

namespace PalomarCorpus.E257.PaperStatementsI
open Set
open scoped BigOperators
open Filter
open Topology
export PalomarCorpus.E257_13.Shared (affineBinaryOrbit erdosSupportSeries integerHalfCarry mobiusCenteredHalfCarry supportCoeff)
/-- States record:257hg-i6, thm:mobius-centred-nonneg from the long record for Erdős problem #257. Transported from Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N := by
  sorry
end PalomarCorpus.E257.PaperStatementsI

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_13.Shared (affineBinaryOrbit erdosSupportSeries greedyMersenneRemainder integerHalfCarry mersenneWeight mobiusCenteredHalfCarry supportCoeff)
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry
/-- States record:257rig-c16, thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  sorry
end PalomarCorpus.E257.PaperStatementsD

namespace PalomarCorpus.E257.PaperStatementsE
open Filter
open Set
open Topology
export PalomarCorpus.E257_13.Shared (affineBinaryOrbit erdosSupportSeries integerHalfCarry mobiusCenteredHalfCarry supportCoeff)
/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsE

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_13.Shared (HalfGreedySkippedFullShellNonnegative affineBinaryOrbit finiteCoeffWindowNumerator greedyHalfFrozenMargin greedyMersennePrefixRat greedyMersenneRemainder greedyMersenneRemainderRat halfGreedyPrefixSupport integerHalfCarry mersenneAchievementSet mersenneWeight mersenneWeightRat mobiusCenteredHalfCarry positiveMersenneSupportValue supportCoeff)
/-- States thm:frozen-margin from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStructuresBJ
open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_13.Shared (HalfGreedySkippedFullShellNonnegative affineBinaryOrbit finiteCoeffWindowNumerator greedyHalfFrozenMargin greedyMersennePrefixRat greedyMersenneRemainder greedyMersenneRemainderRat halfGreedyPrefixSupport integerHalfCarry mersenneAchievementSet mersenneWeight mersenneWeightRat mobiusCenteredHalfCarry positiveMersenneSupportValue supportCoeff)
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- The total weight selected by a Boolean word, namely the sum of those weights whose corresponding entry of the word is true, with the recursion stopping at the end of either list. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- The capacity left unpaid after the greedy Boolean word has been applied to a weight list, namely the capacity minus the weight it selects. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
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
/-- The greedy remainder of the seam subset sum problem at row s, namely the seam capacity minus the total weight selected greedily from the seam weight list. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- Local definition stemBitsFrom, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def stemBitsFrom (s : ℕ) (P : Finset ℕ) : ℕ → List Bool
  | d =>
      if h : d < s then
        decide (d ∈ P) :: stemBitsFrom s P (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- Local definition stemBits, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def stemBits (s : ℕ) (P : Finset ℕ) : List Bool :=
  stemBitsFrom s P 2
/-- Local definition HalfGreedySkippedSeamAlignmentZero, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedSeamAlignmentZero : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n) →
      seamIntegerGreedyRemainder n = 0
/-- Local definition HalfGreedySkippedSeamEscape, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedSeamEscape : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    halfStripBound (2 * n) < seamIntegerGreedyRemainder n
/-- States thm:frozen-margin from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States record:257bm-c14, thm:frozen-margin from the long record for Erdős problem #257. Transported from Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative := by
  sorry
end PalomarCorpus.E257.PaperStructuresBJ

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
export PalomarCorpus.E257_13.Shared (erdosSupportSeries)
/-- States thm:weighted-coeff-engine from the long record for Erdős problem #257. Transported from Erdos249257.irrational_coeff_series_of_weighted_coeff_block_certificates in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_coeff_series_of_weighted_coeff_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  sorry
/-- States thm:factorial-twopow-support from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSum_factorial_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSum_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) := by
  sorry
/-- States thm:lcm-gap-engine from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSum_of_lcm_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSum_of_lcm_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto (fun k => a k - ((Finset.range k).image a).lcm id)
      atTop atTop) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  sorry
/-- States thm:pairwise-coprime from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_pairwise_coprime in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_pairwise_coprime (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAG
