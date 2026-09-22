/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band m

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E249.PaperStatementsM
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States res:fulldepth from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.fullDepth_amplification in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fullDepth_amplification :
    (∀ d N : ℕ, 0 < d →
      (totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) →
      ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
        certifiedKill (t * d) N (t * d) ∨
          certifiedKill ((t + 1) * d) N ((t + 1) * d)) ∧
    (∀ d N : ℕ, 0 < d →
      ((∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
        totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ))) ∧
    ((∀ d : ℕ, 0 < d → ∀ N : ℕ,
        ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsM
