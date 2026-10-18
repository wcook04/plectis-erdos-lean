/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_27

Every non-theorem declaration of `PalomarCorpus/E257_27/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257_27.Shared
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- The finite Boolean support displayed by row `n`. Coordinates zero and one are normalized away at the definition boundary. Local copy of Erdos249257.globalRepairStageSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257_27.Shared

namespace PalomarCorpus.E257.PaperStructuresCJ
open scoped BigOperators
/-- Local definition PerturbedFamily, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily (α : Type*) where
  oldSum : α → ℕ
  pulse : α → ℕ
  gap : ℕ
  pulseCap : ℕ
  gap_pos : 0 < gap
  pulse_le : ∀ x, pulse x ≤ pulseCap
  oldSum_injective : Function.Injective oldSum
  separated : ∀ {x y}, oldSum x < oldSum y →
    oldSum x + gap ≤ oldSum y
  pulseCap_lt_three_gap : pulseCap < 3 * gap
/-- Local definition AdjacentCut, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily.AdjacentCut {α : Type*} (F : PerturbedFamily α) (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x
/-- Local definition abovePulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.abovePulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.above
/-- Local definition belowPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.belowPulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.below
/-- Local definition newCapacity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.newCapacity {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 4 * C + F.gap
/-- Local definition overshoot, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C
/-- Local definition remainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below
/-- Local definition successorCarries, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap
/-- Local definition prefixRemainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.prefixRemainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : ℕ :=
  if K.successorCarries then
    F.gap - (4 * K.overshoot + K.abovePulse)
  else
    4 * K.remainder + F.gap - K.belowPulse
/-- Local definition terminalWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4
/-- Local definition nextRemainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.nextRemainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : ℕ :=
  if K.terminalWeight ≤ K.prefixRemainder then
    K.prefixRemainder - K.terminalWeight
  else
    K.prefixRemainder
/-- Local definition prefixChoice, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.prefixChoice {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : α :=
  if K.successorCarries then K.above else K.below
/-- Local definition newSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.newSum {α : Type*} (F : PerturbedFamily α) (x : α) : ℕ := 4 * F.oldSum x + F.pulse x
end PalomarCorpus.E257.PaperStructuresCJ

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
export PalomarCorpus.E257_27.Shared (CofinalExactLocalMersenneHalfRows ExactLocalMersenneHalfRow localMersenneQuotient localPrefixQuotient mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
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
export PalomarCorpus.E257_27.Shared (CofinalPositiveHalfGreedySkips greedyMersenneRemainderRat mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)
end PalomarCorpus.E257.PaperStatementsD

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_27.Shared (CofinalExactLocalMersenneHalfRows CofinalPositiveHalfGreedySkips ExactLocalMersenneHalfRow greedyMersenneRemainderRat localMersenneQuotient localPrefixQuotient mersenneWeightRat)
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStructuresAW
open Filter
open Set
open scoped BigOperators
export PalomarCorpus.E257_27.Shared (BooleanMobiusGlobalRepairTrajectory globalRepairStageSupport localMersenneQuotient localPrefixQuotient)
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
export PalomarCorpus.E257_27.Shared (BooleanMobiusGlobalRepairTrajectory globalRepairStageSupport)
/-- The diagonal limit bit: inspect coordinate `d` at the first row after which the upper-half rewrites can no longer touch it. Local copy of Erdos249257.globalRepairLimitBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitBit
    (T : BooleanMobiusGlobalRepairTrajectory) (d : ℕ) : Bool :=
  T.bit (2 * d) d
/-- The positive frozen support selected by the diagonal limit word. Local copy of Erdos249257.globalRepairLimitSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) : Set ℕ :=
  {d : ℕ | 2 ≤ d ∧ globalRepairLimitBit T d = true}
end PalomarCorpus.E257.PaperStructuresT
