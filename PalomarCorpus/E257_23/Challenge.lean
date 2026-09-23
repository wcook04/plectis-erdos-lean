/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: a quotient bound at a crossing; filling the remaining binary positions; reducing the dyadic-boundary checks

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
open Finset

namespace PalomarCorpus.E257_23.Shared
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
end PalomarCorpus.E257_23.Shared

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_23.Shared (localBinarySuffix localMersenneQuotient localPrefixQuotient mersenneWeightRat)
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
/-- The genuinely residual part of the predecessor supply: only a skipped rank immediately before an actual take is exposed. Consecutive skipped ranks have a uniform finite-lookahead proof below. Local copy of Erdos249257.HalfGreedyPreTakePrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
/-- The minimal actual-orbit form of the socket: the quotient lower bound is required only when rank `c` is genuinely skipped by the rational half-greedy orbit. Local copy of Erdos249257.HalfGreedySkippedCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)
/-- A one-row-earlier form of the actual skipped-rank socket. At endpoint `2c-3` the relevant binary suffix has half the critical capacity. Local copy of Erdos249257.HalfGreedySkippedPrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedPrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
/-- States record:257bm-c6a from the long record for Erdős problem #257. Transported from Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply := by
  sorry
/-- States record:257bm-c6a from the long record for Erdős problem #257. Transported from Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply := by
  sorry
/-- States record:257bm-c6b from the long record for Erdős problem #257. Transported from Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
    {c t : ℕ} (hc : 4 ≤ c) (htPos : 0 < t) (ht : t ≤ c - 3)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (htake : ∀ j ∈ Finset.range (t - 1),
      mersenneWeightRat (c + j + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c + j))
    (hfuture : greedyMersenneRemainderRat (1 / 2 : ℚ) (c + t - 1) <
      mersenneWeightRat (c + t))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  sorry
/-- States record:257bm-c6a from the long record for Erdős problem #257. Transported from Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfGreedy_precriticalSuffix_lt_of_next_skip
    {c : ℕ} (hc : 6 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (hnext : greedyMersenneRemainderRat (1 / 2 : ℚ) c <
      mersenneWeightRat (c + 1)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  sorry
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStatementsAA
/-- States record:257bm-c6b from the long record for Erdős problem #257. Transported from Erdos249257.sub_two_le_two_pow_sub_four in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sub_two_le_two_pow_sub_four
    {c : ℕ} (hc : 6 ≤ c) :
    c - 2 ≤ 2 ^ (c - 4) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_23.Shared (localBinarySuffix localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- An exact finite Boolean quotient row at endpoint `n`. Local copy of Erdos249257.ExactLocalMersenneHalfRow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The source-current fractional part of `2^M / (2^d - 1)` for `d ≥ 2`. The exponent is reduced modulo `d` before the division. Local copy of Erdos249257.localMersenneFraction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)
/-- Sum of the corresponding fractional contributions. Local copy of Erdos249257.localFractionMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d
/-- States record:257bm-c8 from the long record for Erdős problem #257. Transported from Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
/-- States record:257bm-c7 from the long record for Erdős problem #257. Transported from Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → c < d) ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1 := by
  sorry
/-- States record:257bm-c6b from the long record for Erdős problem #257. Transported from Erdos249257.precriticalCrossingTax_of_futureThreshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem precriticalCrossingTax_of_futureThreshold
    {D : Finset ℕ} {c t : ℕ}
    (hc : 4 ≤ c)
    (ht : t ≤ c - 3)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localFractionMass (insert c D) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := by
  sorry
/-- States record:257bm-c10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_from_skipped_prefix {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) = 2 ^ (2 * c - 3) - 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_23.Shared (localMersenneQuotient)
/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from Erdos249257.exists_boolean_word_of_lt_two_pow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V := by
  sorry
/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStatementsBE
open Finset
/-- `j` indexes the smallest power `2^(d-j+1)` that is still at least `E`. The final disjunction handles the last index, where there is no next power in the band family. Local copy of Erdos249257.HalfUpperResetCriticalBand.CriticalDyadicBandIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)
/-- Avoidance of every width-`2(d+j)` interval immediately below the dyadic power indexed by `j`. Local copy of Erdos249257.HalfUpperResetCriticalBand.DyadicBandEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
/-- States record:257bm-c11 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_eq_top_of_le_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_critical_dyadic_band_index_eq_top_of_le_two {d E j : ℕ}
    (hE : E ≤ 2) (hj : CriticalDyadicBandIndex d E j) :
    j = d := by
  sorry
/-- States record:257bm-c11 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_critical_dyadic_band_index_unique {d E : ℕ}
    (hE : E ≤ 2 ^ (d + 1)) :
    ∃! j : ℕ, CriticalDyadicBandIndex d E j := by
  sorry
/-- States record:257bm-c11 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_boundary_is_smallest in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_critical_dyadic_boundary_is_smallest {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    E ≤ 2 ^ (d - j + 1) ∧
      ∀ i : ℕ, i ≤ d → E ≤ 2 ^ (d - i + 1) →
        (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d - i + 1) := by
  sorry
/-- States record:257bm-c11 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_band_escape_iff_single_test in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_dyadic_band_escape_iff_single_test {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    DyadicBandEscape d E ↔ E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := by
  sorry
end PalomarCorpus.E257.PaperStatementsBE
