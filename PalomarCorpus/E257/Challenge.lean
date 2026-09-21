/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős problem 257: reciprocal Mersenne subseries

Erdős problem 257 asks whether `∑ a ∈ A, 1 / (2 ^ a - 1)` is irrational for
every infinite `A ⊆ ℕ`. The parent problem remains open. This module restates,
with only `Mathlib` in scope, the theorems of this development that have
Comparator grade proof coverage.

The principal theorem is
`ReciprocalSupport.irrational_supportPowerSeries_of_summable_reciprocal`:
every infinite support with summable reciprocals gives an irrational series at
every integer base `b ≥ 2`. Erdős printed the pairwise coprime case at every
integer base in 1968 and stated the removal of coprimality without proof; no
priority over that statement is claimed here.

Three families state criteria that do not ask for reciprocal summability:
`DivisibilityWeightedSupport` (finite prime part weighted mass),
`VariableExponentCover` (strengthened positive fractional divisor covers),
and `MixedWeightedCover` (their common observation scale).
`LiteralWeightedCover` exhibits a weighted host with divergent reciprocal mass
outside every logarithmic budget cover, and `DyadicObservationSummability`
records dyadic averaging estimates for weighted observation masses.

`FinitePeriodNoncollapse` gives exact reduced denominator periods for finite
supports. `RationalTailRigidity` and `BooleanMobiusCarry` give necessary
conditions and exact coordinates for a hypothetical rational value.
`AchievementSetGeometry` and `FairCoding` give the topology, the exact
Lebesgue dichotomy, and the rational fibre null theorem for the achievement
set; perfectness and nowhere density of subsum sets are classical after
Kakeya (1914), and Kovac and Tao record the fixed base Cantor structure.

`GeneralRepairCriterion`, `ScaledGreedyTrap`, `RationalMembership`,
`PositiveSkipEquivalence`, `FourNinthsRepairWindows` and
`TwentyOneFatalBranch` give exact membership criteria; they decide no target.
`TerminalScaledVanishing` and `ActualUpperSuccessor` are conditional: each
unconstructed hypothesis would produce an infinite support of value `1 / 2`.

Narrative lives in `PalomarCorpus/README.md`.
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
/-- Rational fibre measure no go: if 0 is not in J and the value coded by J, that is the sum over m in J of 1 divided by 2 to the power m minus 1, equals a rational number q, then the supported achievement set of J has Lebesgue measure zero. In the hypothesis J indexes exponents and in the conclusion it indexes digit positions. The theorem excludes positive measure selection over a rational fibre; it excludes no individual point and proves no irrationality. -/
theorem volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
    {J : Set ℕ} (hJ0 : 0 ∉ J) {q : ℚ}
    (hvalue : positiveMersenneSupportValue J = (q : ℝ)) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  sorry
/-- Complete geometry and Lebesgue measure classification, for every set J of allowed digit positions and with no hypothesis on J: the supported coding map is injective, its range is compact and nowhere dense, the range is perfect whenever J is infinite, and one of two mutually exclusive cases holds for the measure, which is valued in the extended nonnegative reals; either the complement of J is a finite set F and the measure is the inverse of 2 raised to the cardinality of F, or the complement of J is infinite and the measure is 0. -/
theorem supportedMersenneAchievementSet_geometry_and_volume (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) ∧
      IsCompact (supportedMersenneAchievementSet J) ∧
      IsNowhereDense (supportedMersenneAchievementSet J) ∧
      (J.Infinite → Perfect (supportedMersenneAchievementSet J)) ∧
      ((∃ F : Finset ℕ,
          J = (↑F : Set ℕ)ᶜ ∧
            volume (supportedMersenneAchievementSet J) =
              ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
        (Jᶜ.Infinite ∧
          volume (supportedMersenneAchievementSet J) = 0)) := by
  sorry
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
/-- The terminal packet lower envelope and the pulse free successor lower envelope are equivalent as propositions. This is an exact reformulation of one hypothesis as another; it proves neither. -/
theorem actualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  sorry
/-- Conditional on the pulse free successor lower envelope holding, there is an infinite set A of natural numbers whose base two series with terms 1 divided by 2 to the power a minus 1 equals exactly one half, and the universal irrationality assertion of the parent problem is therefore false. The hypothesis is not constructed anywhere in this development, so this is a conditional implication and the parent problem remains open. -/
theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry
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
/-- If A does not contain 0, contains some positive element, and its base two support series equals p divided by q for an integer p and a positive natural q, then there is an integer sequence U carrying a Boolean Moebius carry certificate for p over q whose Moebius transform selects exactly the set A. -/
theorem exists_booleanMobiusCarry_of_support_fraction
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  sorry
/-- Converse direction: from a Boolean Moebius carry certificate for p over q with q positive, the support selected by the Moebius transform of the carry quotient omits 0 and its base two support series equals exactly p divided by q. -/
theorem support_fraction_of_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧ erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  sorry
/-- Full reconstruction from a Boolean Moebius carry certificate with q positive: the selected support omits 0, the carry quotient coincides with the divisor incidence arithmetic function of that support, the sequence U is a tempered binary carry orbit for those coefficients at modulus q, the Moebius transform selects exactly that support, and its base two support series equals p divided by q. -/
theorem BooleanMobiusCarryCertificate.reconstructsSupport
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ} (hq : 0 < q)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧
      carryQuotientAF q U = supportCoeffAF A ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  sorry
/-- Existence level equivalence for a positive natural q: a normalised nonempty support with base two value exactly p divided by q exists if and only if a Boolean Moebius carry certificate for p over q exists. This is an exact characterisation of rational valued supports; it excludes no rational value, and the reconstructed support is not required to be infinite. -/
theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U := by
  sorry
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
/-- Both clauses of the divisibility weighted claim hold: finite prime part weighted mass at a fixed base b at least 2 on an infinite support avoiding 0 forces irrationality at that base, and finite prime part weighted mass at base 2 on a host avoiding 0 forces irrationality at every integer base at least 2 for every infinite subset of that host. The weighted hypothesis is strictly weaker than summability of the reciprocals of the support, and LiteralWeightedCover.exists_weighted_not_strengthened_host exhibits a weighted host of divergent reciprocal mass. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  sorry
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
/-- Explicit majorant: if alpha is nonnegative on A and the conductor weighted terms of A are summable, then for every finite set J of dyadic levels and every natural Q, the sum over j in J of 2 to the power minus j times the observation mass up to Q times 2 to the power j is at most 2 Q times the total conductor weighted mass. Dyadic averaging estimate for weighted observation masses; no compared theorem here consumes it. -/
theorem dyadic_supportObservationMass_sum_le (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (J : Finset ℕ) (Q : ℕ) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j * supportObservationMass A α (Q * 2 ^ j)) ≤
      2 * (Q : ℝ) * ∑' a : ℕ, weightedObservationTerm A α a := by
  sorry
/-- Under the same nonnegativity and conductor weighted summability hypotheses, and for every natural Q, the sequence indexed by the dyadic level j whose term is 2 to the power minus j times the observation mass up to Q times 2 to the power j is summable. Dyadic averaging estimate for weighted observation masses; no compared theorem here consumes it. -/
theorem summable_dyadic_supportObservationMass (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j *
      supportObservationMass A α (Q * 2 ^ j)) := by
  sorry
/-- Under the same nonnegativity and conductor weighted summability hypotheses, and for every natural Q, the sliding window mean over the dyadic levels from M to 2M minus 1 of 2 to the power minus j times the observation mass up to Q times 2 to the power j, divided by M, tends to 0 as M tends to infinity. Dyadic averaging estimate for weighted observation masses; no compared theorem here consumes it. -/
theorem tendsto_dyadic_supportObservationMass_mean (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M) atTop (nhds 0) := by
  sorry
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
/-- For every finite nonempty set F of exponents with 0 not in F, every integer base b at least 2, and least common multiple of F at least 2, that least common multiple is strictly smaller than the reduced denominator of the finite Erdős sum. This is the strict growth consequence of finite period noncollapse; it is a finite support statement and supplies no infinite support irrationality argument. -/
theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  sorry
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
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
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

namespace PalomarCorpus.E257.MixedWeightedCover
open Set
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)
/-- The mixed support claim, named as a proposition: for every set E with 0 not in E and finite prime part weighted mass at base 2, and every set V admitting a strengthened positive cover, every infinite subset of the union of E and V has irrational support series at every integer base at least 2. -/
noncomputable def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
/-- The mixed support claim holds: a finite prime part weighted host at base 2 avoiding 0 and a strengthened positive cover host together force irrationality at every integer base at least 2 for every infinite subset of their union. The two criteria are combined on one common observation scale, and no individual irrationality premise is assumed. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem mixedSupportClaim : MixedSupportClaim := by
  sorry
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
/-- Every finite rational greedy remainder of the target one half is strictly positive, so no finite greedy prefix represents one half exactly. -/
theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  sorry
/-- The cofinal positive skip condition at one half holds if and only if one half belongs to the base two Mersenne achievement set. This identifies an apparently weaker route with the open endpoint itself; it is an exact reformulation and proves neither side. -/
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
end PalomarCorpus.E257.PositiveSkipEquivalence

namespace PalomarCorpus.E257.RationalMembership
open Set
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
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
/-- Necessary condition under rationality: if A is infinite, v is positive, and the base two support series of A equals p divided by 2 to the power c times v, then there is a sequence u of natural numbers with u at n equal to v times the binary tail of the divisor incidence coefficients of A beyond c+n, with every term strictly positive, with the exact recurrence u at n+1 plus v times the coefficient at c+n+1 equal to twice u at n, with u at n congruent modulo v to the natural truncation of p, multiplied by 2 to the power n, and with u exceeding every natural bound. Unboundedness alone excludes no rational value. No oddness is assumed; the odd in the name refers to the sibling theorem. -/
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  sorry
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
/-- Necessary condition under a dyadic rational value: if A is infinite and its base two support series equals p divided by 2 to the power c, then the reciprocal support terms of A are not summable, or the reciprocal mass of A is strictly greater than 1. The conclusion is a disjunction and produces no contradiction by itself. -/
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
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
/-- If x is nonnegative and does not belong to the base two Mersenne achievement set, then its scaled greedy remainder tends to infinity. This classifies nonmembership dynamics; it establishes nonmembership of no particular target. -/
theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  sorry
/-- For every nonnegative real x, membership in the base two Mersenne achievement set is equivalent to the existence of one bounded cofinal subsequence of the scaled greedy remainder. This is an exact reformulation; it constructs no bounded subsequence. -/
theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  sorry
/-- The base two Mersenne achievement set is exactly the set of nonnegative reals whose scaled greedy remainder stays strictly below the universal barrier 2 at every scale. This is an exact description of the set, not a decision procedure for a given target. -/
theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  sorry
/-- For every nonnegative rational q, membership in the base two Mersenne achievement set is equivalent to cofinal crossing of the moving lower separatrix, that is to twice the scaled greedy remainder falling strictly below the rescaled Mersenne weight at the next rank, at arbitrarily late scales. This is an exact reformulation; it decides no target. -/
theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  sorry
/-- The instance of the rational lower separatrix criterion at the target one over twenty one: membership of one over twenty one in the base two Mersenne achievement set is equivalent to cofinal crossing of the moving lower separatrix for that target. The equivalence proves neither side. -/
theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  sorry
/-- The instance of the cofinal boundedness criterion at the target one over twenty one: membership of one over twenty one in the base two Mersenne achievement set is equivalent to the scaled greedy remainder for that target having one bounded cofinal subsequence. The equivalence proves neither side. -/
theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  sorry
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
/-- Conditional on a terminal scaled vanishing sequence existing, there is an infinite set A of natural numbers whose base two series with terms 1 divided by 2 to the power a minus 1 equals exactly one half, and the universal irrationality assertion of the parent problem is therefore false. No such sequence is constructed here, so this is a conditional implication, it does not place one half in the achievement set, and the parent problem remains open. -/
theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry
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
/-- Closed row canonicalisation: if a Boolean word has the same length as the local Mersenne weight list at binary scale 2R through rank R, its selected weight plus a residual s equals the denominator twenty one capacity at that scale, and the residual satisfies s at most 2 to the power R, then the word is exactly the integer greedy word and s is exactly the greedy remainder. The theorem supplies no closed row. -/
theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen :
      bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits =
        integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  sorry
/-- Conditional on the closed lower state supply condition, one over twenty one belongs to the base two Mersenne achievement set. The hypothesis is not established here. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- Membership of one over twenty one in the base two Mersenne achievement set is equivalent to the failure of the explicit fatal aligned branch. This is an exact dichotomy; it does not show that the fatal branch is impossible. -/
theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch := by
  sorry
/-- Inside the fatal aligned branch, the canonical quotient greedy remainder eventually stays strictly above the closed binary capacity, that is there is a threshold beyond which 2 to the power R is strictly below the greedy remainder at every rank R. This is a consequence within the branch, not a refutation of it. -/
theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R := by
  sorry
/-- Inside the fatal aligned branch, the greedy support and remainder eventually follow one exact affine recurrence: beyond a threshold the support at R+1 is the support at R with the rank R+1 inserted, and the remainder at R+1 equals four times the remainder at R plus the target two step pulse at binary scale 2R, minus the two step divisor pulse of the support at that scale, and then minus the sum of 2 to the power R+1 and 1. Both subtractions are truncated natural subtraction and are taken in that order. This classifies the surviving regime without excluding it. -/
theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) := by
  sorry
end PalomarCorpus.E257.TwentyOneFatalBranch

namespace PalomarCorpus.E257.VariableExponentCover
open Set
export PalomarCorpus.E257.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)
/-- The strengthened positive cover claim, named as a proposition: for every positive cover datum satisfying the strengthened one inverse power cost condition, every infinite subset of its host has irrational support series at every integer base at least 2. -/
noncomputable def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
/-- The strengthened positive cover claim holds: a positive fractional divisor cover with variable exponents that are positive and at most 1, nonnegative coefficients, convergent columns, divisor majorisation, and convergent one inverse power cost forces irrationality at every integer base at least 2 for every infinite subset of its host. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim := by
  sorry
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
/-- An infinite positive support satisfying the finite-prime weighted condition has strictly positive displacements below every ε > 0 at arbitrarily large indices, for every base b ≥ 2. -/
theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε := by
  sorry
end PalomarCorpus.E257.WeightedCloseReturn
