/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_47

Every non-theorem declaration of `PalomarCorpus/E257_47/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open ArithmeticFunction
open Set
open scoped ArithmeticFunction.Moebius
open scoped ENNReal
open MeasureTheory
open scoped Classical
open scoped BigOperators

namespace PalomarCorpus.E257_47.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
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
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
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
/-- The integer capacity of the denominator twenty one quotient problem at binary scale M, namely the natural number quotient of 2 to the power M by 21. -/
noncomputable def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21
/-- Weighted sum of a Boolean word. The equal-length hypotheses below make the two fallback equations irrelevant. Local copy of Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- The capacity left unpaid by the integer greedy rule on the local Mersenne weights at binary scale 2R through rank R against the denominator twenty one capacity at that scale. -/
noncomputable def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))
/-- Minimal asymptotic form of the quotient route. No fixed cap is built into the statement: the normalized deterministic defect (with only a linear support-cardinality allowance) must tend to zero along one unbounded sequence of rows. Local copy of Erdos249257.TwentyOneCofinalEvenQuotientGreedyDecay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def TwentyOneCofinalEvenQuotientGreedyDecay : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      Tendsto
        (fun k : ℕ =>
          ((twentyOneEvenQuotientGreedyRemainder (R k) +
              (2 * R k + 1) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k))
        atTop (nhds 0)
end PalomarCorpus.E257_47.Shared

namespace PalomarCorpus.E257.PaperStatementsBC
open Filter
open Topology
export PalomarCorpus.E257_47.Shared (erdosSupportSeries supportCoeff)
/-- The paper's terminal carry, with its sum reindexed from `j = 2, ..., M` to `j = 0, ..., M - 2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.terminalPaperCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def terminalPaperCarry (A : Set ℕ) (M : ℕ) : ℤ :=
  (2 : ℤ) ^ (M - 1) -
    ∑ j ∈ Finset.range (M - 1),
      (2 : ℤ) ^ (M - 2 - j) * (supportCoeff A (j + 2) : ℤ)
/-- The full prime-power part determined by a finite set of primes. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p
/-- The literal weighted term at an integer base. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))
/-- The weighted hypothesis, not its irrationality conclusion. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))
end PalomarCorpus.E257.PaperStatementsBC

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
export PalomarCorpus.E257_47.Shared (erdosSupportSeries)
/-- The reciprocal summand of a support, with exponent zero harmlessly normalized to zero by real division. Local copy of Erdos249257.reciprocalSupportTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
end PalomarCorpus.E257.PaperStatementsAV

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsM
open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_47.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)
/-- Integer numerator of the same dyadic prefix at denominator `2^N`. Local copy of Erdos249257.binaryCoeffPrefixNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)
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
/-- Local copy of ErdosProblems.Erdos257.PaperCompleteR20.paperIntegerDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperIntegerDefect (x : ℝ) (N : ℕ) : ℤ :=
  ⌊(2 : ℝ)^N*x⌋ - binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N
end PalomarCorpus.E257.PaperStatementsM

namespace PalomarCorpus.E257.PaperStructuresBM
open Filter
open Set
open scoped Classical
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_47.Shared (TwentyOneCofinalEvenQuotientGreedyDecay integerGreedyBits integerGreedyRemainder localMersenneQuotient localMersenneWeights localMersenneWeightsFrom mersenneAchievementSet mersenneWeight positiveMersenneSupportValue twentyOneEvenQuotientGreedyRemainder twentyOneQuotientTarget weightedBoolSum)
end PalomarCorpus.E257.PaperStructuresBM

namespace PalomarCorpus.E257.PaperStructuresBQ
open Filter
open Set
open scoped Classical
open scoped BigOperators
export PalomarCorpus.E257_47.Shared (TwentyOneCofinalEvenQuotientGreedyDecay integerGreedyBits integerGreedyRemainder localMersenneQuotient localMersenneWeights localMersenneWeightsFrom twentyOneEvenQuotientGreedyRemainder twentyOneQuotientTarget weightedBoolSum)
end PalomarCorpus.E257.PaperStructuresBQ
