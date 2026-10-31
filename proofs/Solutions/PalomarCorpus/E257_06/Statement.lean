/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_06

Every non-theorem declaration of `PalomarCorpus/E257_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E257_06.Shared
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The quotient pulse contributed by rank d between consecutive seam rows at row s, namely 1 if d divides 2s+2, plus twice 1 if d divides 2s+1, and 0 for the nondividing cases. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- `D` is the paper's `D_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the largest sum at most `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowLower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)
/-- `B` is the paper's `B_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the smallest sum strictly greater than `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowUpper, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
end PalomarCorpus.E257_06.Shared

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_06.Shared (IsRowLower IsRowUpper localMersenneQuotient localPrefixQuotient rowPulse seamSubsetTarget truncatedMersenneWeight)
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStructuresAZ
open scoped BigOperators
export PalomarCorpus.E257_06.Shared (IsRowLower IsRowUpper localMersenneQuotient localPrefixQuotient rowPulse seamSubsetTarget truncatedMersenneWeight)
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local definition toNatWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
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
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Local definition rowSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)
/-- Local definition greedySupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)
end PalomarCorpus.E257.PaperStructuresAZ
