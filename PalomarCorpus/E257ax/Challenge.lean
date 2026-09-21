/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band x

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Set
open Filter
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsAX
open Set
open Filter
open scoped BigOperators
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
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- The binary-boundary target before any selected divisor weights are removed. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The weights with indices `d,d+1,…,s-1`, in descending size order. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The actual proper-divisor weight word, indexed by `2,…,s-1`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- The natural exponent support encoded by a finite seam word. Local copy of Erdos249257.seamWordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- `d` is the largest false rank of a seam word: it is absent, and every strictly larger rank still inside the row is present. Local copy of Erdos249257.IsLargestFalseRank, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLargestFalseRank {s : ℕ} (b : SeamRowWord s) (d : ℕ) : Prop :=
  2 ≤ d ∧ d < s ∧
    d ∉ seamWordSupport b ∧
      ∀ e : ℕ, d < e → e < s → e ∈ seamWordSupport b
/-- Row `s` has a largest false rank strictly beyond two thirds of the row. Local copy of Erdos249257.LargestSkipLateAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def LargestSkipLateAt (s : ℕ) : Prop :=
  ∃ d : ℕ,
    IsLargestFalseRank (seamGreedyWord s) d ∧ 2 * s < 3 * d
/-- The seam target `T_s = 2^{2s-1} - 2^s` on the quotient scale `4^s`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.seamScaledTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamScaledTarget (s : ℕ) : ℝ :=
  (seamSubsetTarget s : ℝ) / (4 : ℝ) ^ s
/-- The truncated integer weight `q(2s,d) = ⌊4^s/(2^d-1)⌋` on the quotient scale `4^s`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.seamScaledWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamScaledWeight (s d : ℕ) : ℝ :=
  (truncatedMersenneWeight s d : ℝ) / (4 : ℝ) ^ s
/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight system `v`, in increasing order of rank, starting at rank `2`. `tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m
/-- States thm:largest-skip-late from the long record for Erdős problem #257. Transported from Erdos249257.largestSkipLateAt_fourteen in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem largestSkipLateAt_fourteen : LargestSkipLateAt 14 := by
  sorry
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.mem_seamGreedySupport_iff_scaled in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_seamGreedySupport_iff_scaled {s d : ℕ} (hs : 2 ≤ s) (h2 : 2 ≤ d)
    (hd : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s)
      ↔ seamScaledWeight s d
          ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) (d - 2) := by
  sorry
/-- States record:257bm-k-dich from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
/-- States record:257bm-k-dich from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_example_six_and_eleven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6 := by
  sorry
/-- States record:257bm-k4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_returning_endpoint_may_fail_to_grow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAX
