/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, the paper structures CI, paper structures CO and positive skip equivalence families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Finset
open Filter
open Topology
open Set
open Filter Set

namespace PalomarCorpus.E257_51.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The P part of a, namely the product over the primes p in the finite set P of p raised to the exponent of p in the factorisation of a. -/
noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p
/-- The weighted term attached to an exponent a at base b, namely the P part of a divided by the product of a and b raised to the P part of a minus 1. -/
noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))
end PalomarCorpus.E257_51.Shared

namespace PalomarCorpus.E257.PaperStructuresCI
open Finset
open Filter
open Topology
export PalomarCorpus.E257_51.Shared (erdosSupportSeries primeSetPart primeWeightedTerm)
/-- The weighted hypothesis, not its irrationality conclusion. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))
/-- Data for a positive fractional divisor cover: a sequence of finite frames of positive integers (frame j, with 0 not in it), exponents alpha j with 0 < alpha j and alpha j at most 1, and nonnegative coefficients c j d with each column sum over d of c j d / d convergent, subject to the divisor majorisation that for every frame index j and every n at least 1 the number of members of frame j dividing n, raised to the power alpha j, is at most the sum of c j d over the divisors d of n. -/
structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
/-- A set A of exponents has a strengthened positive cover when some positive cover data has A inside its host and satisfies the strengthened one inverse power cost condition. -/
noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable
/-- Local definition HasOldPositiveCover, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HasOldPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.OldCostSummable
/-- States res:weighted-cover-incomparability from the short record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR8.exists_strengthened_not_old_or_weighted_host in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_strengthened_not_old_or_weighted_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A ∧
      (¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  sorry
end PalomarCorpus.E257.PaperStructuresCI

namespace PalomarCorpus.E257.PaperStructuresCO
open Filter
open Topology
export PalomarCorpus.E257_51.Shared (erdosSupportSeries primeSetPart primeWeightedTerm)
/-- States prop:257-finite-witness-rule from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.finite_monotone_witness_rule_realised in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_monotone_witness_rule_realised
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∃ H : Set ℕ, 0 ∉ H ∧
      (∀ b : ℕ, 2 ≤ b → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
        (Summable (Set.indicator H (primeWeightedTerm b P)) ↔ U (P ∩ E))) ∧
      ¬ Summable (Set.indicator H (fun a : ℕ => (1 : ℝ) / a)) ∧
      (∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)) := by
  sorry
end PalomarCorpus.E257.PaperStructuresCO

namespace PalomarCorpus.E257.PositiveSkipEquivalence
open Set
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
/-- Every finite rational greedy remainder of the target one half is strictly positive, so no finite greedy prefix represents one half exactly. -/
theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  sorry
end PalomarCorpus.E257.PositiveSkipEquivalence

namespace PalomarCorpus.E257.RationalMembership
open Set
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
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
/-- The set of positive ranks that the greedy Mersenne rule on x does not select. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- For every real x, the set of positive ranks skipped by the greedy Mersenne rule on x is infinite if and only if for every K there is an n at least K at which the weight at n+1 exceeds the greedy remainder after rank n. Supporting reformulation of infinitude as a cofinal condition. -/
theorem greedyMersenneSkippedSupport_infinite_iff_cofinal_skips (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  sorry
/-- If a rational q belongs to the base two Mersenne achievement set, then the greedy Mersenne rule on q skips infinitely many positive ranks. This is the forward implication of the rational membership criterion. -/
theorem infinite_greedyMersenneSkippedSupport_of_rat_mem
    {q : ℚ} (hmem : (q : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  sorry
/-- For every nonnegative rational q, membership of q in the base two Mersenne achievement set is equivalent to the greedy Mersenne rule on q skipping infinitely many positive ranks. This is an exact reformulation; it constructs no such support and decides no target. -/
theorem rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  sorry
/-- For every nonnegative rational q, membership of q in the base two Mersenne achievement set is equivalent to the greedy rule skipping at arbitrarily late ranks, that is to the condition that for every K some n at least K has the weight at n+1 exceeding the greedy remainder after rank n. This is an exact reformulation; it decides no target. -/
theorem rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (q : ℝ) n := by
  sorry
end PalomarCorpus.E257.RationalMembership

namespace PalomarCorpus.E257.RationalTailRigidity
open Filter Set
export PalomarCorpus.E257_51.Shared (erdosSupportSeries)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- A zero window of length h beginning after N for a natural coefficient sequence f: f vanishes at N+j+1 for every j below h. -/
noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0
/-- A zero window of length h beginning after N for the divisor incidence coefficients of A, that is a stretch of h consecutive integers after N none of which has a divisor in A. -/
noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h
/-- The reciprocal support summand at a, namely 1 divided by a when a lies in A and 0 otherwise; the exponent a = 0 contributes 0. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The reciprocal mass of A, namely the sum over a in A of 1 divided by a, taken as an unconditional sum of the reciprocal support terms. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a
/-- The multiplicative order of 2 modulo an odd positive integer v, formed from the unit that the oddness of v determines. -/
noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ :=
  orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd))
/-- Necessary condition under rationality: if A contains a positive element, v is positive, and the base two support series of A equals p divided by 2 to the power c times v, then for every positive epsilon there is a nonnegative constant B such that every zero window of the divisor incidence coefficients beginning at c+N has length at most B plus epsilon times the base two logarithm of N+1. The constant depends on the displayed rationality data, and infinitude of A is not assumed. -/
theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  sorry
/-- Necessary condition under rationality: if A contains a positive element, its reciprocal support terms are summable, v is odd and greater than 1, the natural truncation of p is coprime to v, and the base two support series of A equals p divided by 2 to the power c times v, then the reciprocal mass of A is at least the reciprocal of the multiplicative order of 2 modulo v. Infinitude of A is absent from the hypotheses, so the bound also applies to finite supports. -/
theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  sorry
end PalomarCorpus.E257.RationalTailRigidity

namespace PalomarCorpus.E257.ReciprocalSupport
/-- The reciprocal support summand at a, namely 1 divided by a when a lies in A and 0 otherwise; the exponent a = 0 contributes 0. -/
noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0. -/
noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- Principal theorem of this entry: for every integer base b at least 2 and every infinite set A of natural numbers whose reciprocal support terms are summable, the series with terms 1 divided by b to the power a minus 1, summed over a in A, is irrational. The support is arbitrary subject to infinitude and reciprocal summability; no pairwise coprimality, periodicity, density, or powerful support hypothesis appears. Erdős printed the pairwise coprime case at every integer base in 1968 and stated the removal of coprimality without printing its proof. -/
theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) :
    Irrational (supportPowerSeries b A) := by
  sorry
end PalomarCorpus.E257.ReciprocalSupport
