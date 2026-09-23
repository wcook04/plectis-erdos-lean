/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.2: exact identities and reductions (part 3 of 5)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Set
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open scoped Classical

namespace PalomarCorpus.E257.PaperStatementsG
open Set
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open scoped Classical
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- A greedy state is fatal when its residual is already larger than all remaining Mersenne mass. Local copy of Erdos249257.GreedyMersenneFatalAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- `M` is the final exponent skipped by the actual greedy half orbit. Local copy of Erdos249257.IsLastHalfGreedySkip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLastHalfGreedySkip (M : ℕ) : Prop :=
  M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
    ∀ m, M < m → m ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ)
/-- States thm:last-skip-iff-fatal from the long record for Erdős problem #257. Transported from Erdos249257.isLastHalfGreedySkip_iff_skip_and_fatal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M := by
  sorry
end PalomarCorpus.E257.PaperStatementsG

namespace PalomarCorpus.E257.PaperStatementsAA
/-- The paper's row-weight functional `W_s(E) = ∑_{e ∈ E} ⌊4^s/(2^e − 1)⌋`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rowWeightSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowWeightSum (s : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ e ∈ E, ⌊(4 : ℝ) ^ s / ((2 : ℝ) ^ e - 1)⌋
/-- States lem:largest-false-rank-algebra from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.largest_false_rank_algebra in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem largest_false_rank_algebra {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * rowWeightSum s (insert d u) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA
