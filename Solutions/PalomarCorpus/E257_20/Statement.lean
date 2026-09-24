/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_20

Every non-theorem declaration of `PalomarCorpus/E257_20/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257_20.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
end PalomarCorpus.E257_20.Shared

namespace PalomarCorpus.E257.PaperStructuresBJ
open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition extend, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Local definition integerGreedyBits_length, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [integerGreedyBits]
      split <;> simp [ih]
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
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
/-- Local definition seamWeightsFrom_eq_cons, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_eq_cons {s d : ℕ} (h : d < s) :
    seamWeightsFrom s d =
      truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
  rw [seamWeightsFrom]
  simp [h]
/-- Local definition seamWeightsFrom_eq_nil, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_eq_nil {s d : ℕ} (h : s ≤ d) :
    seamWeightsFrom s d = [] := by
  rw [seamWeightsFrom]
  simp [Nat.not_lt.mpr h]
/-- Local definition seamWeightsFrom_length_eq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega
/-- Local definition seamWeights_length_eq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  unfold seamWeights
  exact seamWeightsFrom_length_eq s 2
/-- Local definition seamGreedyWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
end PalomarCorpus.E257.PaperStructuresBJ

namespace PalomarCorpus.E257.PaperStatementsAH
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight)
/-- The first two geometric channels of the Mersenne tail. This cap is strictly weaker than the dyadic cap while still lying below the full tail. Local copy of Erdos249257.halfTwoChannelCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
end PalomarCorpus.E257.PaperStatementsAH

namespace PalomarCorpus.E257.PaperStructuresU
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- **Packet §4.** A finite support word certified to straddle the target at depth `d`: the coded value is at most `t` and the value plus the complete unresolved tail mass still reaches `t`. This is deliberately *weaker* than the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap of the correction image with the cylinder, not containment inside it. Local copy of Erdos249257.IsStraddlePrefix, restated so the compared statements elaborate against Mathlib alone. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
end PalomarCorpus.E257.PaperStructuresU

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
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
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257.PaperStatementsD
