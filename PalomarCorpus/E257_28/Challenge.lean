/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: one-step quotient identities; bounds for the remaining binary positions; doubling the endpoint

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open Topology
open Set
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257_28.Shared
/-- The divisor incidence of a finite set D of ranks at n, namely the number of members of D that divide n. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
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
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
end PalomarCorpus.E257_28.Shared

namespace PalomarCorpus.E257.PaperStatementsAK
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (endpointDivisorContribution localBinarySuffix localMersenneQuotient localPrefixQuotient)
/-- The integer target corresponding to the dyadic value immediately below `1/2` at endpoint scale `2^M`. Local copy of Erdos249257.halfEndpointTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfEndpointTarget (M : ℕ) : ℕ :=
  2 ^ (M - 1) - 1
/-- The signed finite-row defect from the integer immediately below one half. Unlike `localBinarySuffix`, this definition never truncates subtraction. Local copy of Erdos249257.localEndpointDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localEndpointDefect (D : Finset ℕ) (M : ℕ) : ℤ :=
  (halfEndpointTarget M : ℤ) - (localPrefixQuotient D M : ℤ)
/-- The next signed Boolean--Möbius coefficient supplied by the binary carry recurrence. Local copy of Erdos249257.localRepairInteger, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)
/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d) := by
  sorry
/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0) := by
  sorry
/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0 := by
  sorry
/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1) := by
  sorry
/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) := by
  sorry
/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) := by
  sorry
/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAK

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (endpointDivisorContribution localMersenneQuotient localPrefixQuotient)
/-- States record:257bm-i1b from the long record for Erdős problem #257. Transported from Erdos249257.localPrefixQuotient_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1) := by
  sorry
/-- States record:257bm-i-rank2 from the long record for Erdős problem #257. Transported from Erdos249257.two_mem_of_exact_localMersenneQuotient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStatementsAN
open scoped BigOperators
open Filter
open Topology
export PalomarCorpus.E257_28.Shared (endpointDivisorContribution)
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finiteErdosSum_den_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_series_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_half_representing_support_is_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_half_representing_support_is_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite := by
  sorry
end PalomarCorpus.E257.PaperStatementsAN

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (localBinarySuffix localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- States record:257bm-i9 from the long record for Erdős problem #257. Transported from Erdos249257.abs_localMersennePrefixValue_sub_half_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_localMersennePrefixValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  sorry
/-- States record:257bm-i7 from the long record for Erdős problem #257. Transported from Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → n < d) ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1 := by
  sorry
/-- States record:257bm-i7 from the long record for Erdős problem #257. Transported from Erdos249257.localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * n - 1) < 2 ^ (n - 1) := by
  sorry
/-- States record:257bm-i5 from the long record for Erdős problem #257. Transported from Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) := by
  sorry
/-- States record:257bm-i6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_capacity_band_exclusion {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D.card ≤ c - 2 ∧ c - 2 ≤ 2 ^ (c - 2) ∧
      (Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3))).card = c - 2 ∧
      (localBinarySuffix D 1 (2 * c - 2) ∉
          Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3)) →
        localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAS
open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_28.Shared (localBinarySuffix localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- States record:257bm-i6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharper_additive_estimate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card := by
  sorry
/-- States record:257bm-i6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAS

namespace PalomarCorpus.E257.PaperStructuresAY
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (localMersenneQuotient)
/-- Descending local quotient weights with ranks `d,d+1,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega
/-- The complete lower quotient word on ranks `2,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2
/-- Number of binary suffix values available after a truncation at depth `M`, when ranks through `R` have already been fixed. Local copy of Erdos249257.BooleanMobiusGreedyReduction.lowerBinaryWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lowerBinaryWindow (M R : ℕ) : ℕ :=
  2 ^ (M - R)
/-- Every head exceeds the sum of its complete tail by at least `gap`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.GapDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws
/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d) := by
  sorry
/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R) := by
  sorry
end PalomarCorpus.E257.PaperStructuresAY
