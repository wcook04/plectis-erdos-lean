/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_09

Every non-theorem declaration of `PalomarCorpus/E257_09/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E257.PaperStructuresBJ
open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
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
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
end PalomarCorpus.E257.PaperStructuresBJ
