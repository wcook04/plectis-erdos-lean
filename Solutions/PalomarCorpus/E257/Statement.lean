/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257

Every non-theorem declaration of `PalomarCorpus/E257/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped ENNReal
open Set MeasureTheory
open Set
open scoped BigOperators
open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius
open Filter Topology
open Set MeasureTheory Topology
open Filter Set

namespace PalomarCorpus.E257.Shared
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
/-- The binary prefix numerator of a coefficient sequence c at scale N, defined by P 0 = 0 and P (N+1) = 2 P N + c (N+1), so that P N is the sum over n from 1 to N of c n times 2 raised to N minus n. -/
noncomputable def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)
noncomputable def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)
noncomputable def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The universal assertion of the parent problem, named as a proposition so that conditional theorems can refer to it: for every infinite set A of natural numbers the base two series with terms 1 divided by 2 to the power a minus 1, summed over a in A, is irrational. Nothing in this development asserts this proposition. -/
noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)
noncomputable def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}
/-- A set A of exponents has a strengthened positive cover when some positive cover data has A inside its host and satisfies the strengthened one inverse power cost condition. -/
noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
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
/-- The set of ranks selected by the greedy Mersenne rule on x, namely the positive m for which the weight at m is at most the greedy remainder after rank m minus 1. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The set of positive ranks that the greedy Mersenne rule on x does not select. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
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
/-- The divisor incidence coefficient of A at n, namely the number of divisors of n that belong to A; it is 0 at n = 0. These coefficients are the base b expansion coefficients of the support series, in the sense that the series equals the sum over n at least 1 of this coefficient divided by b to the power n; they can exceed b minus 1, so they are not digits in general. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257.Shared

namespace PalomarCorpus.E257.AchievementSetGeometry
open scoped ENNReal
open Set MeasureTheory
export PalomarCorpus.E257.Shared (mersenneWeight positiveMersenneSupportValue)
/-- The contribution of the k th binary digit of a digit string b, namely the value of that digit, 0 or 1, times the Mersenne weight at k+1. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The real value coded by a binary digit string b, namely the sum over k at least 0 of the k th digit times the Mersenne weight at k+1. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- The subtype of binary digit strings that vanish outside a prescribed set J of allowed digit positions. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The coding map on digit strings supported in J, sending such a string to the real number it codes. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The supported Mersenne achievement set of J, namely the range of the coding map on binary digit strings vanishing outside J; it is the set of subsums of the Mersenne series that use only the digit positions in J. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
end PalomarCorpus.E257.AchievementSetGeometry

namespace PalomarCorpus.E257.ActualUpperSuccessor
open Set
open scoped BigOperators
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries integerGreedyBits)
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
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
noncomputable def seamWeights (s : ℕ) : List ℕ := seamWeightsFrom s 2
/-- The total weight selected by a Boolean word, namely the sum of the weights at the positions where the word is true; positions beyond the shorter of the two lists contribute nothing. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | w :: ws, b :: bs => (if b then w else 0) + weightedBoolSum ws bs
/-- The capacity left unpaid after the greedy Boolean word has been applied to a weight list, namely the capacity minus the weight it selects. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- The greedy remainder of the seam subset sum problem at row s, namely the seam capacity minus the total weight selected greedily from the seam weight list. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- The quotient pulse contributed by rank d between consecutive seam rows at row s, namely 1 if d divides 2s+2, plus twice 1 if d divides 2s+1, and 0 for the nondividing cases. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- The greedy Boolean word produced by the seam weight list at row s against the seam capacity at row s. -/
noncomputable def seamGreedyBits (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)
/-- The greedy bit at rank d of the seam word at row s, read at list position d minus 2 with truncated natural subtraction, so the ranks 0, 1 and 2 all read position 0, and with value false when that position lies outside the word. -/
noncomputable def seamGreedyBit (s d : ℕ) : Bool :=
  (seamGreedyBits s).getD (d - 2) false
/-- The total pulse carried by the selected ranks below the seam at row s, namely the sum of the row pulse over the ranks from 2 to s minus 1 whose greedy bit is true; the index range is s minus 2 in truncated natural subtraction, so the sum is empty and the value is 0 when s is at most 2. -/
noncomputable def seamBelowPulse (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if seamGreedyBit s (i + 2) then rowPulse s (i + 2) else 0
/-- A two field record used for an adjacent seam cut, with a proposition field successorCarries and a natural number field belowPulse. The structure imposes no relation between the two fields; seamAdjacentCut supplies the values they carry. -/
structure SeamAdjacentCutView where
  successorCarries : Prop
  belowPulse : ℕ
/-- The adjacent cut view at seam row s, for s at least 5: its proposition field states that the first s minus 2 bits of the greedy word at row s+1 differ from the greedy word at row s, and its numeric field is the pulse below the seam at row s. -/
noncomputable def seamAdjacentCut (s : ℕ) (_hs : 5 ≤ s) : SeamAdjacentCutView where
  successorCarries :=
    (seamGreedyBits (s + 1)).take (s - 2) ≠ seamGreedyBits s
  belowPulse := seamBelowPulse s
/-- The charge accumulated along a realised right run driven by a pulse sequence, defined by charge 0 = 0 and charge (k+1) = 4 times charge k, plus the pulse at k, plus 4. -/
noncomputable def affineRightRunCharge (pulse : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * affineRightRunCharge pulse k + pulse k + 4
/-- The terminal packet lower envelope, named as a proposition: for all d and k with 5 at most d, needed to form the adjacent cut, with 13 at most d and k at most d, if the adjacent cut at d has a changed successor prefix and if at every step q below k the right run recurrence holds, that is the seam greedy remainder at d+q+2 plus 2 to the power d+q+2 plus the pulse below the seam at row d+q+1 plus 4 equals 4 times the seam greedy remainder at d+q+1, then 4 to the power k times 2 times the sum of d and k is at most the seam greedy remainder at d+k+1 plus the affine right run charge built from the pulses below the seam at the rows d+q+1. This names a hypothesis and asserts nothing. -/
noncomputable def SeamActualUpperRightPacketLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    4 ^ k * (2 * (d + k)) ≤
      seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k
/-- The pulse free successor lower envelope, named as a proposition: under the same bounds on d and k, the same changed successor prefix and the same right run recurrence below k, the quantity 2 to the power d+1 less 2 raised to the exponent d minus k plus 1, then increased by 2 times the sum of d and k, is at most the seam greedy remainder at d+1. Both subtractions are truncated natural subtraction, and k at most d keeps the subtracted power at most the leading one. This names a hypothesis and asserts nothing. -/
noncomputable def SeamActualUpperSuccessorLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    2 ^ (d + 1) - 2 ^ (d - k + 1) + 2 * (d + k) ≤
      seamIntegerGreedyRemainder (d + 1)
end PalomarCorpus.E257.ActualUpperSuccessor

namespace PalomarCorpus.E257.BooleanMobiusCarry
open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius
export PalomarCorpus.E257.Shared (erdosSupportSeries supportCoeff)
/-- The tempered binary carry orbit condition for an integer sequence u attached to a coefficient sequence c and a natural number v, with no positivity imposed on v: the exact recurrence u (N+1) = 2 u N minus v times c (N+1) holds for every N, and u N divided by 2 to the power N tends to 0. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The divisor incidence coefficient of A viewed as an integer valued arithmetic function, with value 0 at 0. -/
noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩
/-- The positive support selected by the Dirichlet Moebius transform of an arithmetic function f, namely the set of n at least 1 at which the convolution of the Moebius function with f takes the value 1. -/
noncomputable def booleanMobiusSupport (f : ArithmeticFunction ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1}
/-- The normalised integer carry quotient of a sequence U at modulus q, namely 0 at n = 0 and otherwise the Lean integer quotient of the difference 2 * U (n-1) - U n by q. Lean integer division is Euclidean, so this is the exact quotient when q divides that difference, it rounds toward minus infinity for q at least 1 when q does not divide it, and it is 0 when q = 0. The certificates below impose that divisibility, so on their domain the value is the exact quotient. -/
noncomputable def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)
/-- The carry quotient viewed as an integer valued arithmetic function. -/
noncomputable def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩
/-- A Boolean Moebius carry certificate for a rational p over q and an integer sequence U: U starts at p, every term is strictly positive, U at N is at most q multiplied by the sum of 2 times the real square root of N and 4, q divides 2 * U N - U (N+1) for every N, and the Dirichlet convolution of the Moebius function with the carry quotient takes only the values 0 and 1 at every positive argument. -/
structure BooleanMobiusCarryCertificate
    (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1
end PalomarCorpus.E257.BooleanMobiusCarry

namespace PalomarCorpus.E257.DivisibilityWeightedSupport
open Set
export PalomarCorpus.E257.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)
/-- The divisibility weighted claim, named as a proposition with two clauses: first, for every integer base b at least 2 and every infinite A not containing 0 with finite prime part weighted mass at base b, the base b support series of A is irrational; second, for every host H not containing 0 with finite prime part weighted mass at base 2, every infinite subset of H has irrational support series at every integer base at least 2. -/
noncomputable def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
end PalomarCorpus.E257.DivisibilityWeightedSupport

namespace PalomarCorpus.E257.DyadicObservationSummability
open Filter Topology
/-- The observation mass of A with weights alpha up to scale R, namely the sum of alpha a over the positive elements a of A that are at most R. -/
noncomputable def supportObservationMass (A : Set ℕ) (α : ℕ → ℝ) (R : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (Finset.range (R + 1)).filter (fun a => 0 < a ∧ a ∈ A), α a
/-- The conductor weighted observation term at a, namely alpha a divided by a when a is positive and lies in A, and 0 otherwise. -/
noncomputable def weightedObservationTerm (A : Set ℕ) (α : ℕ → ℝ) (a : ℕ) : ℝ := by
  classical
  exact if 0 < a ∧ a ∈ A then α a / a else 0
end PalomarCorpus.E257.DyadicObservationSummability

namespace PalomarCorpus.E257.FairCoding
open Set MeasureTheory Topology
open scoped ENNReal
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
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
end PalomarCorpus.E257.FairCoding

namespace PalomarCorpus.E257.FinitePeriodNoncollapse
/-- The literal finite Erdős sum as a rational number, namely the sum over n in the finite set F of 1 divided by b to the power n minus 1, computed in the rationals; the exponent n = 0 contributes 0. -/
noncomputable def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)
end PalomarCorpus.E257.FinitePeriodNoncollapse

namespace PalomarCorpus.E257.FourNinthsRepairWindows
open Set
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
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
end PalomarCorpus.E257.FourNinthsRepairWindows

namespace PalomarCorpus.E257.GeneralRepairCriterion
open Set
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
/-- The greedy defect of a target x at scale N, namely the natural number floor of 2 to the power N times x, which is 0 when that product is negative, minus the binary prefix numerator of the divisor incidence coefficients of the greedy Mersenne support of x, computed with truncated natural subtraction. It is one sequence of natural numbers attached to the target. -/
noncomputable def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N
end PalomarCorpus.E257.GeneralRepairCriterion

namespace PalomarCorpus.E257.LiteralWeightedCover
open Set
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)
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
end PalomarCorpus.E257.LiteralWeightedCover

namespace PalomarCorpus.E257.MixedWeightedCover
open Set
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)
/-- The mixed support claim, named as a proposition: for every set E with 0 not in E and finite prime part weighted mass at base 2, and every set V admitting a strengthened positive cover, every infinite subset of the union of E and V has irrational support series at every integer base at least 2. -/
noncomputable def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
end PalomarCorpus.E257.MixedWeightedCover

namespace PalomarCorpus.E257.PositiveSkipEquivalence
open Set
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
/-- The rational greedy Mersenne remainder of a rational target x through rank n, computed exactly in the rationals: it starts at x and at each rank n+1 subtracts the rational weight 1 divided by 2 to the power n+1 minus 1 exactly when that weight is at most the current remainder. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- The cofinal positive skip condition at the target one half, named as a proposition: for every N there is a rank c at least the maximum of N and 4 whose preceding rational greedy remainder is strictly positive and strictly below the rational Mersenne weight at c, so that the greedy rule skips rank c from a positive remainder. -/
noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c
end PalomarCorpus.E257.PositiveSkipEquivalence

namespace PalomarCorpus.E257.RationalMembership
open Set
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
end PalomarCorpus.E257.RationalMembership

namespace PalomarCorpus.E257.RationalTailRigidity
open Filter Set
export PalomarCorpus.E257.Shared (erdosSupportSeries supportCoeff)
/-- The binary tail of a coefficient sequence c beyond scale N, namely the sum over j at least 0 of c at N+j+1 divided by 2 to the power j+1. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
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
end PalomarCorpus.E257.RationalTailRigidity

namespace PalomarCorpus.E257.ReciprocalSupport
/-- The reciprocal support summand at a, namely 1 divided by a when a lies in A and 0 otherwise; the exponent a = 0 contributes 0. -/
noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0. -/
noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.ReciprocalSupport

namespace PalomarCorpus.E257.ScaledGreedyTrap
open Set
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E257.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- The greedy remainder of x at scale N rescaled by the binary place value, namely 2 to the power N times the greedy Mersenne remainder of x after rank N. -/
noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * greedyMersenneRemainder x N
/-- The rescaled Mersenne weight at rank n, namely 2 to the power n divided by 2 to the power n minus 1; at n = 0 the value is 0. -/
noncomputable def mersenneScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * mersenneWeight n
/-- The cofinal lower branch condition for x, named as a proposition: for every K there is an N at least K at which twice the scaled greedy remainder of x at N is strictly below the rescaled Mersenne weight at N+1. -/
noncomputable def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    2 * scaledGreedyRemainder x N < mersenneScale (N + 1)
/-- The cofinal boundedness condition for x, named as a proposition: there is a real bound B such that for every K some N at least K has scaled greedy remainder at most B. No global bound on the orbit is required. -/
noncomputable def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ scaledGreedyRemainder x N ≤ B
end PalomarCorpus.E257.ScaledGreedyTrap

namespace PalomarCorpus.E257.TerminalScaledVanishing
open Filter Set
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries supportCoeff)
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- A Boolean support word through depth N, that is a Boolean valued function on the ranks 0 up to N. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set of ranks represented by a finite Boolean word, namely the ranks below its depth plus one at which the word is true. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- The terminal scaled vanishing hypothesis packaged as a structure: a sequence of depths and of Boolean support words at those depths, with every depth at least 1, depths tending to infinity, ranks 0 and 1 excluded from every word, and the absolute integer half carry of the word evaluated at depth minus one, divided by 2 to the power of that depth, tending to 0. No compatibility between successive words is required. -/
structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ depth n)
      atTop (nhds 0)
end PalomarCorpus.E257.TerminalScaledVanishing

namespace PalomarCorpus.E257.TwentyOneFatalBranch
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport integerGreedyBits mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The fatal condition for a target x at rank n: the greedy Mersenne remainder after rank n strictly exceeds the whole remaining Mersenne tail, so the remainder can no longer be exhausted by later ranks. -/
noncomputable def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n
/-- The total weight selected by a Boolean word, namely the sum of those weights whose corresponding entry of the word is true, with the recursion stopping at the end of either list. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- The capacity left unpaid after the greedy Boolean word has been applied to a weight list, namely the capacity minus the total weight selected greedily. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The divisor incidence of a finite set D of ranks at n, namely the number of members of D that divide n. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The list of local Mersenne quotients at binary scale M for the ranks from the given starting index up to R, in increasing rank order. -/
noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega
/-- The local Mersenne weight list at binary scale M through rank R, namely the local quotients for the ranks 2 up to R. -/
noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2
/-- The finite set of ranks selected by a Boolean word read from a given starting rank, collecting each rank whose bit is true. -/
noncomputable def lowerSupportFromBits : ℕ → List Bool → Finset ℕ
  | _, [] => ∅
  | d, false :: bits => lowerSupportFromBits (d + 1) bits
  | d, true :: bits => insert d (lowerSupportFromBits (d + 1) bits)
/-- The integer capacity of the denominator twenty one quotient problem at binary scale M, namely the natural number quotient of 2 to the power M by 21. -/
noncomputable def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21
/-- The Boolean word produced by running the exact rational greedy Mersenne rule on a rational target for a prescribed number of ranks starting at a given rank, taking a rank exactly when its rational Mersenne weight is at most the current remainder. -/
noncomputable def rationalMersenneGreedyBitsFrom : ℕ → ℕ → ℚ → List Bool
  | _, 0, _ => []
  | d, n + 1, x =>
      if mersenneWeightRat d ≤ x then
        true ::
          rationalMersenneGreedyBitsFrom (d + 1) n
            (x - mersenneWeightRat d)
      else
        false :: rationalMersenneGreedyBitsFrom (d + 1) n x
/-- The set of ranks selected by the integer greedy rule on the local Mersenne weights at binary scale 2R through rank R against the denominator twenty one capacity at that scale. -/
noncomputable def twentyOneEvenQuotientGreedySupport (R : ℕ) : Finset ℕ :=
  lowerSupportFromBits 2
    (integerGreedyBits
      (localMersenneWeights (2 * R) R)
      (twentyOneQuotientTarget (2 * R)))
/-- The capacity left unpaid by the integer greedy rule on the local Mersenne weights at binary scale 2R through rank R against the denominator twenty one capacity at that scale. -/
noncomputable def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))
/-- The two step divisor pulse of a finite set D of ranks at binary scale M, namely twice the divisor incidence of D at M+1 plus the divisor incidence of D at M+2. -/
noncomputable def localPrefixTwoStepPulse (D : Finset ℕ) (M : ℕ) : ℕ :=
  2 * endpointDivisorContribution D (M + 1) +
    endpointDivisorContribution D (M + 2)
/-- The two step pulse of the denominator twenty one target at binary scale M, namely the natural number quotient of 4 times the residue of 2 to the power M modulo 21 by 21. -/
noncomputable def twentyOneTargetTwoStepPulse (M : ℕ) : ℕ :=
  4 * (2 ^ M % 21) / 21
/-- The closed lower state supply condition, named as a proposition: for every R at least 2 there are a finite set D of ranks between 2 and R and a residual s with the local prefix quotient of D at binary scale 2R plus s equal to the denominator twenty one capacity at that scale and with s at most 2 to the power R. -/
noncomputable def TwentyOneClosedLowerStateSupply : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∃ D : Finset ℕ, ∃ s : ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ R) ∧
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) ∧
      s ≤ 2 ^ R
/-- The eventual doubling block condition, named as a proposition: from some threshold onward, every K admits a rank n with K strictly below n, n at most twice K, and n selected by the greedy Mersenne rule on the target one over twenty one. -/
noncomputable def TwentyOneGreedyEventuallyHitsDoublingBlocks : Prop :=
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)
/-- The explicit fatal aligned branch for the target one over twenty one, named as a proposition: there are a rank n and a threshold at which the greedy rule is fatal at n, only finitely many positive ranks are skipped, every rank after n is selected, the integer greedy word on the full local Mersenne weights agrees with the exact rational greedy word at every sufficiently large even scale, and the eventual doubling block condition holds. -/
noncomputable def TwentyOneFatalAlignedBranch : Prop :=
  ∃ n R₀ : ℕ,
    GreedyMersenneFatalAt (1 / 21 : ℝ) n ∧
      (greedyMersenneSkippedSupport (1 / 21 : ℝ)).Finite ∧
      (∀ k : ℕ,
        n + k + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ)) ∧
      (∀ R : ℕ, R₀ ≤ R →
        integerGreedyBits
            (localMersenneWeights (2 * R) (2 * R))
            (twentyOneQuotientTarget (2 * R)) =
          rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) ∧
      TwentyOneGreedyEventuallyHitsDoublingBlocks
end PalomarCorpus.E257.TwentyOneFatalBranch

namespace PalomarCorpus.E257.VariableExponentCover
open Set
export PalomarCorpus.E257.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)
/-- The strengthened positive cover claim, named as a proposition: for every positive cover datum satisfying the strengthened one inverse power cost condition, every infinite subset of its host has irrational support series at every integer base at least 2. -/
noncomputable def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
end PalomarCorpus.E257.VariableExponentCover

namespace PalomarCorpus.E257.WeightedCloseReturn
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E257.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)
/-- For a positive divisor d, the radix atom b^(N mod d)/(b^d − 1); defined to be zero at d = 0. -/
noncomputable def shiftedRadixAtom (b N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1)
/-- The shifted radix atom restricted by the indicator of the support A. -/
noncomputable def shiftedRadixSupportAtom
    (b : ℕ) (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedRadixAtom b N) d
/-- The shifted support-atom sum minus the original support series. -/
noncomputable def displacement (b : ℕ) (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑' d : ℕ, shiftedRadixSupportAtom b A N d) - erdosSupportSeries b A
end PalomarCorpus.E257.WeightedCloseReturn
