/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_02

Every non-theorem declaration of `PalomarCorpus/E257_02/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E257_02.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős-Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257_02.Shared

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_02.Shared (erdosBorweinMersenneConstant mersenneAchievementSet mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- Binary digit strings supported on `J`. Local copy of ErdosProblems.Erdos257.SupportedMersenneDigits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The ordinary Mersenne digit map restricted to a chosen support. Local copy of ErdosProblems.Erdos257.supportedMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The achievement set obtained by allowing digits only on `J`. Local copy of ErdosProblems.Erdos257.supportedMersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_02.Shared (erdosBorweinMersenneConstant mersenneAchievementSet mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- Literal finite internal gap over a positive finite prefix. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.InternalMersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m
end PalomarCorpus.E257.PaperStatementsD

namespace PalomarCorpus.E257.PaperStatementsC
open scoped BigOperators
/-- Every head exceeds the sum of its complete tail by at least `gap`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.GapDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Weighted sum of a Boolean word. The equal-length hypotheses below make the two fallback equations irrelevant. Local copy of Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
end PalomarCorpus.E257.PaperStatementsC

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
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
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
end PalomarCorpus.E257.PaperStatementsF
