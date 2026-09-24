/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, the fair coding, finite period noncollapse and four ninths repair windows families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Set MeasureTheory Topology
open scoped ENNReal
open Set

namespace PalomarCorpus.E257_50.Shared
/-- Integer numerator of the same dyadic prefix at denominator `2^N`. Local copy of Erdos249257.binaryCoeffPrefixNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)
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
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_50.Shared

namespace PalomarCorpus.E257.FairCoding
open Set MeasureTheory Topology
open scoped ENNReal
export PalomarCorpus.E257_50.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- Binary digit strings, that is functions from the naturals to the two element type. -/
noncomputable abbrev Digits := ℕ → Fin 2
/-- The contribution of the k th binary digit of a digit string b, namely the value of that digit, 0 or 1, times the Mersenne weight at k+1. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : Digits) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The real value coded by a binary digit string, namely the sum over k at least 0 of the k th digit times the Mersenne weight at k+1. -/
noncomputable def positiveMersenneDigitValue (b : Digits) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- The fair coin measure on the two element type, namely one half of the Dirac mass at 0 plus one half of the Dirac mass at 1. -/
noncomputable def fairCoin : Measure (Fin 2) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1
/-- The fair product measure on binary digit strings, namely the countable infinite product of copies of the fair coin measure. -/
noncomputable def fairDigits : Measure Digits :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)
/-- The pushforward of the fair product measure on binary digit strings along the Mersenne coding map is exactly Lebesgue measure restricted to the base two Mersenne achievement set. -/
theorem fairCoding_pushforward_eq_volume_restrict :
    Measure.map positiveMersenneDigitValue fairDigits =
      volume.restrict mersenneAchievementSet := by
  sorry
/-- The Mersenne coding map is measure preserving from the fair product measure on binary digit strings to Lebesgue measure restricted to the base two Mersenne achievement set. -/
theorem measurePreserving_fairCoding :
    MeasurePreserving positiveMersenneDigitValue fairDigits
      (volume.restrict mersenneAchievementSet) := by
  sorry
/-- The set of binary digit strings whose Mersenne coded value is rational has fair product measure 0. This says that rational values are exceptional for the coding; it decides no particular rational value. -/
theorem fairCoding_rational_values_null :
    fairDigits
        (positiveMersenneDigitValue ⁻¹' Set.range (fun q : ℚ => (q : ℝ))) =
      0 := by
  sorry
end PalomarCorpus.E257.FairCoding

namespace PalomarCorpus.E257.FinitePeriodNoncollapse
/-- The literal finite Erdős sum as a rational number, namely the sum over n in the finite set F of 1 divided by b to the power n minus 1, computed in the rationals; the exponent n = 0 contributes 0. -/
noncomputable def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)
/-- For every finite nonempty set F of exponents with 0 not in F and every integer base b at least 2, the base b is coprime to the reduced denominator of the finite Erdős sum, and the multiplicative order of b modulo that reduced denominator is exactly the least common multiple of F. The statement packages the coprimality witness existentially because the order is stated through the unit it determines. Reduction to lowest terms therefore destroys no part of the finite period. -/
theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  sorry
end PalomarCorpus.E257.FinitePeriodNoncollapse

namespace PalomarCorpus.E257.FourNinthsRepairWindows
open Set
export PalomarCorpus.E257_50.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
/-- The binary floor of four ninths at scale N, namely the natural number quotient of 4 times 2 to the power N by 9, which is the integer part of 2 to the power N times four ninths. -/
noncomputable def fourNinthsBinaryFloor (N : ℕ) : ℕ :=
  4 * 2 ^ N / 9
/-- The greedy defect of the target four ninths at scale N, namely its binary floor at N minus the binary prefix numerator of the divisor incidence coefficients of the greedy support of four ninths, computed with truncated natural subtraction. -/
noncomputable def fourNinthsGreedyDefect (N : ℕ) : ℕ :=
  fourNinthsBinaryFloor N -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ))) N
/-- The one step repair condition at scale N for the target four ninths: the greedy defect at N+1 is at most the greedy defect at N, compared as integers. -/
noncomputable def FourNinthsOneStepRepairSucc (N : ℕ) : Prop :=
  (fourNinthsGreedyDefect (N + 1) : ℤ) ≤ (fourNinthsGreedyDefect N : ℤ)
/-- The cofinal repair condition for the target four ninths: for every K there is an N at least K at which the one step repair condition holds. -/
noncomputable def FourNinthsOneStepRepairCofinal : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ FourNinthsOneStepRepairSucc N
/-- Supporting lemma: a sequence Q of natural numbers with Q at N at most the sum of 2 times the real square root of N and 4 at every N cannot strictly increase throughout a window of length 2 times the integer square root of K plus 12, so for every K there is an N with K at most N, N below K plus 2 times the integer square root of K plus 12, and Q at N+1 at most Q at N. -/
theorem exists_repair_in_sqrt_window
    (Q : ℕ → ℕ)
    (hQ : ∀ N, (Q N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4)
    (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧ Q (N + 1) ≤ Q N := by
  sorry
/-- Four ninths belongs to the base two Mersenne achievement set if and only if the cofinal one step repair condition holds for four ninths. This is an exact reformulation of the membership question; it proves neither side. -/
theorem four_ninths_mem_iff_repairCofinal :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔ FourNinthsOneStepRepairCofinal := by
  sorry
/-- Four ninths belongs to the base two Mersenne achievement set if and only if, for every K, some N with K at most N and N below K plus 2 times the integer square root of K plus 12 satisfies the one step repair condition. This localises the membership question to an explicit finite window at each scale; it proves neither side. -/
theorem four_ninths_mem_iff_repair_sqrt_windows :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        FourNinthsOneStepRepairSucc N := by
  sorry
/-- Exclusion criterion: if there is a K for which the greedy defect of four ninths strictly increases at every N with K at most N and N below K plus 2 times the integer square root of K plus 12, then four ninths does not belong to the base two Mersenne achievement set. No such window is exhibited here. -/
theorem four_ninths_not_mem_of_strict_sqrt_window
    (K : ℕ)
    (h : ∀ N, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      fourNinthsGreedyDefect N < fourNinthsGreedyDefect (N + 1)) :
    (4 / 9 : ℝ) ∉ mersenneAchievementSet := by
  sorry
end PalomarCorpus.E257.FourNinthsRepairWindows

namespace PalomarCorpus.E257.GeneralRepairCriterion
open Set
export PalomarCorpus.E257_50.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
/-- The greedy defect of a target x at scale N, namely the natural number floor of 2 to the power N times x, which is 0 when that product is negative, minus the binary prefix numerator of the divisor incidence coefficients of the greedy Mersenne support of x, computed with truncated natural subtraction. It is one sequence of natural numbers attached to the target. -/
noncomputable def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N
/-- For every nonnegative real x, membership of x in the base two Mersenne achievement set is equivalent to cofinal non increase of its greedy defect, that is to the condition that for every K there is an N at least K with the defect at N+1 at most the defect at N. This replaces a quantifier over supports by a pointwise inequality on one integer sequence; it decides no particular target. -/
theorem mem_iff_greedyBinaryDefect_cofinal_repairs {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  sorry
/-- For every nonnegative real x, membership of x in the base two Mersenne achievement set is equivalent to the same non increase occurring at some N inside every window from K up to K plus 2 times the integer square root of K plus 12. The window constant is the one carried by the divisor bound in the proof; the criterion decides no particular target. -/
theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  sorry
end PalomarCorpus.E257.GeneralRepairCriterion

namespace PalomarCorpus.E257.LiteralWeightedCover
open Set
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
/-- The finite prime part weighted hypothesis at base b: there is a finite nonempty set P of primes for which the weighted terms of A, that is the P part of a divided by a times b raised to the P part of a minus 1, form a summable family. This names the hypothesis, not any irrationality conclusion. -/
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
/-- The cost C j of frame j of a positive cover, namely the sum over d of c j d divided by d; the d = 0 summand is zero because division by zero is zero here. -/
noncomputable def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)
/-- The host of a positive cover, namely the set of positive integers that belong to at least one of its frames. -/
noncomputable def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}
/-- The strengthened one inverse power cover cost condition: the sum over frame indices j of C j times 2 raised to the power (j+1) times alpha j, divided by 2 raised to alpha j minus 1, converges. -/
noncomputable def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))
/-- A set A of exponents has a strengthened positive cover when some positive cover data has A inside its host and satisfies the strengthened one inverse power cost condition. -/
noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable
/-- Arbitrary weight positive cover data on a prescribed support A: finite frames avoiding 0, strictly positive frame weights summing to 1, exponents alpha j with 0 < alpha j and alpha j at most 1, nonnegative coefficients with convergent columns, the requirement that every element of A lies in some frame, the divisor majorisation of the fractional frame incidence by the coefficient divisor sums, and convergence of the logarithmic budget whose j th term is the frame cost divided by the weight raised to alpha j and by 2 raised to alpha j minus 1. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))
/-- There is an infinite set A of positive exponents with 0 not in A that has finite prime part weighted mass at base 2, has divergent reciprocal mass, admits no strengthened positive cover, admits no logarithmic budget cover at all, and all of whose infinite subsets have irrational support series at every integer base at least 2. This witnesses that the finite prime part weighted hypothesis reaches supports of divergent reciprocal mass and that those supports need not lie in the strengthened cover class. -/
theorem exists_weighted_not_strengthened_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      ¬ HasStrengthenedPositiveCover A ∧ IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  sorry
/-- There is an infinite set A of positive exponents with 0 not in A that has finite prime part weighted mass at base 2, admits no logarithmic budget cover, and yet can be combined with an arbitrary strengthened positive cover host V so that every infinite subset of the union of A and V has irrational support series at every integer base at least 2. No existence of a cover host is assumed as a hypothesis; the conclusion quantifies over every such host. -/
theorem exists_weighted_obstruction_with_mixed_heredity :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ V : Set ℕ, HasStrengthenedPositiveCover V →
        ∀ B : Set ℕ, B ⊆ A ∪ V → B.Infinite → ∀ b : ℕ, 2 ≤ b →
          Irrational (erdosSupportSeries b B)) := by
  sorry
end PalomarCorpus.E257.LiteralWeightedCover

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
