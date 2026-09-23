/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_40

Every non-theorem declaration of `PalomarCorpus/E257_40/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E257_40.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257_40.Shared

namespace PalomarCorpus.E257.AchievementSetGeometry
open scoped ENNReal
open Set MeasureTheory
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The contribution of the k th binary digit of a digit string b, namely the value of that digit, 0 or 1, times the Mersenne weight at k+1. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The real value coded by a binary digit string b, namely the sum over k at least 0 of the k th digit times the Mersenne weight at k+1. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
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
export PalomarCorpus.E257_40.Shared (erdosSupportSeries)
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
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
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
/-- The universal assertion of the parent problem, named as a proposition so that conditional theorems can refer to it: for every infinite set A of natural numbers the base two series with terms 1 divided by 2 to the power a minus 1, summed over a in A, is irrational. Nothing in this development asserts this proposition. -/
noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)
end PalomarCorpus.E257.ActualUpperSuccessor

namespace PalomarCorpus.E257.BooleanMobiusCarry
open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius
export PalomarCorpus.E257_40.Shared (erdosSupportSeries)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
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
