/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.5: obstructions and countermodels

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators

namespace PalomarCorpus.E257_33.Shared
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- An exact finite Boolean quotient row at endpoint `n`. Local copy of Erdos249257.ExactLocalMersenneHalfRow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
end PalomarCorpus.E257_33.Shared

namespace PalomarCorpus.E257.PaperStatementsAA
/-- A one-point predicate satisfying the same endpoint transition shape as `exactLocalMersenneHalfRow_double_or_recycle`. It is the smallest explicit falsifier for any attempt to infer cofinal exact rows from that dichotomy alone: at endpoint six the recycling arm may return to endpoint six through `c = 4` forever. Local copy of Erdos249257.boundedDoubleOrRecycleModel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def boundedDoubleOrRecycleModel (n : ℕ) : Prop := n = 6
/-- States record:257bm-k1 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_bounded_double_or_recycle_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_bounded_double_or_recycle_countermodel :
    (∀ n : ℕ, boundedDoubleOrRecycleModel n ↔ n = 6) ∧
      boundedDoubleOrRecycleModel 6 ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        boundedDoubleOrRecycleModel (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2)) ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        4 ≤ 4 ∧ 4 ≤ n ∧ boundedDoubleOrRecycleModel (2 * 4 - 2)) ∧
      ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ boundedDoubleOrRecycleModel n) := by
  sorry
/-- States record:257bm-k1, record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n := by
  sorry
/-- States record:257bm-k9 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_det_eq_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_relationInvariant_channels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    Matrix.det (fun i j : ι => channel j (row i)) = 0 := by
  sorry
/-- States record:257bm-k9 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_33.Shared (localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The source-current fractional part of `2^M / (2^d - 1)` for `d ≥ 2`. The exponent is reduced modulo `d` before the division. Local copy of Erdos249257.localMersenneFraction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)
/-- Sum of the corresponding fractional contributions. Local copy of Erdos249257.localFractionMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d
/-- States record:257bm-k-dich from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_row_value_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ) := by
  sorry
/-- States record:257bm-k2 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_not_necessary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5 := by
  sorry
/-- States record:257bm-k2 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_suffices_for_sharp_capacity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAX
open scoped BigOperators
open Filter
open Set
export PalomarCorpus.E257_33.Shared (ExactLocalMersenneHalfRow localMersenneQuotient localPrefixQuotient)
/-- States record:257bm-k-dich from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
/-- States record:257bm-k-dich from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_example_six_and_eleven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6 := by
  sorry
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_returning_endpoint_may_fail_to_grow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAX

namespace PalomarCorpus.E257.PaperStatementsAS
open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (ExactLocalMersenneHalfRow localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAS

namespace PalomarCorpus.E257.PaperStructuresBG
open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- An exact row together with a protected below-half core. Every support rank outside the core lies strictly above `cutoff`, and the current endpoint lies below `2 * cutoff`. These two inequalities force the next first crossing to occur late enough to give strict endpoint progress. Local copy of Erdos249257.ProtectedExactLocalMersenneRow, restated so the compared statements elaborate against Mathlib alone. -/
structure ProtectedExactLocalMersenneRow where
  endpoint : ℕ
  cutoff : ℕ
  support : Finset ℕ
  core : Finset ℕ
  endpoint_six : 6 ≤ endpoint
  cutoff_four : 4 ≤ cutoff
  core_subset : core ⊆ support
  new_above_cutoff : ∀ d ∈ support, d ∉ core → cutoff < d
  core_bounds : ∀ d ∈ core, 2 ≤ d ∧ d ≤ cutoff
  support_bounds : ∀ d ∈ support, 2 ≤ d ∧ d ≤ endpoint
  exact_quotient :
    localPrefixQuotient support endpoint = 2 ^ (endpoint - 1) - 1
  core_below_half : localMersennePrefixValue core < (1 / 2 : ℚ)
  two_mem_core : 2 ∈ core
  endpoint_lt_twice_cutoff : endpoint < 2 * cutoff
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_crossing_beyond_cutoff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_protected_row_crossing_beyond_cutoff
    (s : ProtectedExactLocalMersenneRow) {e : ℕ} (heSupport : e ∈ s.support)
    (heCross : (1 / 2 : ℚ) <
      localMersennePrefixValue (insert e (s.support.filter fun d => d < e))) :
    s.cutoff < e := by
  sorry
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_endpoint_growth in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_protected_row_endpoint_growth
    (s : ProtectedExactLocalMersenneRow) {c : ℕ} (hc : s.cutoff < c) :
    s.endpoint < 2 * c - 2 := by
  sorry
end PalomarCorpus.E257.PaperStructuresBG

namespace PalomarCorpus.E257.PaperStatementsK
open scoped BigOperators
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_33.Shared (localMersennePrefixValue mersenneWeightRat)
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
/-- States record:257rig-k6 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1) := by
  sorry
end PalomarCorpus.E257.PaperStatementsK

namespace PalomarCorpus.E257.PaperStatementsL
open Filter
open Set
open Topology
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- States record:257hg-k12 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsL
