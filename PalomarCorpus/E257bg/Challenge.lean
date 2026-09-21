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

open Filter
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsBG
open Filter
open scoped BigOperators
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
/-- The integer capacity remaining after the descending greedy of `integerGreedyBits` has processed the first `m` weights of `ws`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def listGreedyRemAfter : ℕ → List ℕ → ℕ → ℕ
  | 0, _, C => C
  | _ + 1, [], C => C
  | m + 1, w :: ws, C => listGreedyRemAfter m ws (if w ≤ C then C - w else C)
/-- The integer residual of the seam greedy after its first `m` ranks. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamIntRem (s m : ℕ) : ℕ :=
  listGreedyRemAfter m (seamWeights s) (seamSubsetTarget s)
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
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
  sorry
end PalomarCorpus.E257.PaperStatementsBG
