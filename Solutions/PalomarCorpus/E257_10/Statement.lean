/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_10

Every non-theorem declaration of `PalomarCorpus/E257_10/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresBL
open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology
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
/-- Local definition overshoot, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C
/-- Local definition remainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below
/-- Local definition successorCarries, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap
/-- Local definition terminalWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local definition toNatWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Local definition wordWeightSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0
/-- The quotient pulse contributed by rank d between consecutive seam rows at row s, namely 1 if d divides 2s+2, plus twice 1 if d divides 2s+1, and 0 for the nondividing cases. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- Local definition wordPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- The total weight selected by a Boolean word, namely the sum of those weights whose corresponding entry of the word is true, with the recursion stopping at the end of either list. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- The capacity left unpaid after the greedy Boolean word has been applied to a weight list, namely the capacity minus the weight it selects. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
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
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- The greedy remainder of the seam subset sum problem at row s, namely the seam capacity minus the total weight selected greedily from the seam weight list. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- Local definition seamGreedyNormalizedRemainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyNormalizedRemainder (s : ℕ) : ℝ :=
  (seamIntegerGreedyRemainder s : ℝ) / (4 : ℝ) ^ s
/-- Local definition SeamGreedyRemainderSubquadraticAlong, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyRemainderSubquadraticAlong (rows : ℕ → ℕ) : Prop :=
  Tendsto rows atTop atTop ∧
    Tendsto (fun j => seamGreedyNormalizedRemainder (rows j))
      atTop (nhds 0)
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
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- Local definition greedyHalfTargetValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def greedyHalfTargetValue : ℝ :=
  positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ))
/-- Local definition seamGreedyLimitDeficit, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyLimitDeficit : ℝ := 1 / 2 - greedyHalfTargetValue
end PalomarCorpus.E257.PaperStructuresBL
