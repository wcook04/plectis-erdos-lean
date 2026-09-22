/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band g

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
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
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  sorry
/-- States thm:last-skip-iff-fatal from the long record for Erdős problem #257. Transported from Erdos249257.isLastHalfGreedySkip_iff_skip_and_fatal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M := by
  sorry
end PalomarCorpus.E257.PaperStatementsG
