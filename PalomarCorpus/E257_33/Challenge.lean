/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: square-root bounds for half-carries; a margin at an unspecified later horizon; equivalent conditions for infinitely many greedy skips

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257_33.Shared
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The binary tail of a coefficient sequence c beyond scale N, namely the sum over j at least 0 of c at N+j+1 divided by 2 to the power j+1. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
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
/-- The set of ranks selected by the greedy Mersenne rule on x, namely the positive m for which the weight at m is at most the greedy remainder after rank m minus 1. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
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
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
end PalomarCorpus.E257_33.Shared

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (affineBinaryOrbit greedyMersennePrefixRat greedyMersenneRemainder greedyMersenneRemainderRat greedyMersenneSupport halfGreedyPrefixSupport integerHalfCarry mersenneWeight mersenneWeightRat mobiusCenteredHalfCarry supportCoeff)
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- Binary capacity carried by skipped support bits in the next `J` rows. The earliest skip receives the largest binary weight. Local copy of Erdos249257.HalfCylinderFiniteShadow.futureSkipCapacity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def futureSkipCapacity
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * futureSkipCapacity A n J +
        (by
          classical
          exact if n + J + 1 ∈ A then 0 else 1)
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- States record:257rig-c18 from the long record for Erdős problem #257. Transported from Erdos249257.halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
    {c : ℕ} (hc : 4 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
        (futureSkipCapacity
          (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ) := by
  sorry
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
export PalomarCorpus.E257_33.Shared (binaryCoeffTail supportCoeff)
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_coeffTail_le_index_add_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_coeffTail_le_index_add_two (A : Set ℕ) (m : ℕ) :
    binaryCoeffTail (supportCoeff A) m ≤ (m : ℝ) + 2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsN
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (affineBinaryOrbit binaryCoeffTail greedyMersennePrefixRat greedyMersenneRemainder greedyMersenneRemainderRat greedyMersenneSupport halfGreedyPrefixSupport integerHalfCarry mersenneWeight mersenneWeightRat mobiusCenteredHalfCarry supportCoeff)
/-- Integer numerator of the frozen coefficient window. The recurrence uses the binary weights `2^(J-i)` without division. Local copy of Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J` future divisor-incidence rows cover the centered carry at depth `k`. Local copy of Erdos249257.greedyHalfFrozenMargin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := by
  sorry
end PalomarCorpus.E257.PaperStatementsN

namespace PalomarCorpus.E257.PaperStatementsB
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (greedyMersenneRemainder greedyMersenneSupport mersenneWeight)
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States record:257bm-c20 from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet := by
  sorry
end PalomarCorpus.E257.PaperStatementsB
