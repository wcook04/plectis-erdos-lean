/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 5.6: dynamics

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
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
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀ := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀ := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1) := by
  sorry
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
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  sorry
end PalomarCorpus.E257.PaperStructuresAZ
