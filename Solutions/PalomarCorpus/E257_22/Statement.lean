/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_22

Every non-theorem declaration of `PalomarCorpus/E257_22/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_22.Shared
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- The finite Boolean support displayed by row `n`. Coordinates zero and one are normalized away at the definition boundary. Local copy of Erdos249257.globalRepairStageSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true
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
/-- Exact Boolean quotient rows occur at arbitrarily large endpoints. No compatibility is imposed between the witnesses at different endpoints. Local copy of Erdos249257.CofinalExactLocalMersenneHalfRows, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
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
/-- The cofinal positive skip condition at the target one half, named as a proposition: for every N there is a rank c at least the maximum of N and 4 whose preceding rational greedy remainder is strictly positive and strictly below the rational Mersenne weight at c, so that the greedy rule skips rank c from a positive remainder. -/
noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The remaining arithmetic socket in the protected-core construction. Whenever a below-half core is crossed by rank `c`, adjoining `c` must already reach the integral half target at endpoint `2c-2`. By `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`, this is exactly the sharp `c-2`-bit capacity needed by the strict-upper skipped-core fill. The deficit hypothesis records that `c` is a genuine crossing rank. Local copy of Erdos249257.SkippedCoreCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257_22.Shared

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_22.Shared (CofinalExactLocalMersenneHalfRows ExactLocalMersenneHalfRow SkippedCoreCriticalQuotientSupply localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
/-- The real Mersenne value carried by a finite exact-row support. Local copy of Erdos249257.exactLocalMersenneRowValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exactLocalMersenneRowValue (D : Finset ℕ) : ℝ :=
  ((localMersennePrefixValue D : ℚ) : ℝ)
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_22.Shared (CofinalPositiveHalfGreedySkips greedyMersenneRemainderRat mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
end PalomarCorpus.E257.PaperStatementsD

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_22.Shared (CofinalExactLocalMersenneHalfRows CofinalPositiveHalfGreedySkips ExactLocalMersenneHalfRow SkippedCoreCriticalQuotientSupply greedyMersenneRemainderRat localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- The minimal actual-orbit form of the socket: the quotient lower bound is required only when rank `c` is genuinely skipped by the rational half-greedy orbit. Local copy of Erdos249257.HalfGreedySkippedCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStructuresAW
open Filter
open Set
open scoped BigOperators
export PalomarCorpus.E257_22.Shared (BooleanMobiusGlobalRepairTrajectory globalRepairStageSupport localMersenneQuotient localPrefixQuotient)
/-- Number of selected lower ranks which divide the next endpoint. Local copy of Erdos249257.endpointDivisorContribution, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The part of row `n` which is already frozen before its upper-half rewrite. Local copy of Erdos249257.globalRepairLowerSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLowerSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (globalRepairStageSupport bit n).filter fun d ↦ d ≤ n / 2
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The next signed Boolean--Möbius coefficient supplied by the binary carry recurrence. Local copy of Erdos249257.localRepairInteger, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)
end PalomarCorpus.E257.PaperStructuresAW

namespace PalomarCorpus.E257.PaperStructuresT
open Filter
open Set
open scoped BigOperators
export PalomarCorpus.E257_22.Shared (BooleanMobiusGlobalRepairTrajectory globalRepairStageSupport)
/-- The diagonal limit bit: inspect coordinate `d` at the first row after which the upper-half rewrites can no longer touch it. Local copy of Erdos249257.globalRepairLimitBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitBit
    (T : BooleanMobiusGlobalRepairTrajectory) (d : ℕ) : Bool :=
  T.bit (2 * d) d
/-- The positive frozen support selected by the diagonal limit word. Local copy of Erdos249257.globalRepairLimitSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) : Set ℕ :=
  {d : ℕ | 2 ≤ d ∧ globalRepairLimitBit T d = true}
end PalomarCorpus.E257.PaperStructuresT

namespace PalomarCorpus.E257.PaperStructuresW
open Filter
open Set
open scoped BigOperators
export PalomarCorpus.E257_22.Shared (BooleanMobiusGlobalRepairTrajectory)
end PalomarCorpus.E257.PaperStructuresW

namespace PalomarCorpus.E257.PaperStructuresBA
open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_22.Shared (SkippedCoreCriticalQuotientSupply localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)
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
end PalomarCorpus.E257.PaperStructuresBA
