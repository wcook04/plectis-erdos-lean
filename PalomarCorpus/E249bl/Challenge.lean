/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band l

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped Classical
open Finset

namespace PalomarCorpus.E249.PaperStatementsBL
open scoped Classical
open Finset
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- First additive character of the infinite tail difference. Local copy of Erdos249257.TotientTailPeriodKiller.tailOrbitFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)
/-- `α_h = (2^h - 1) S`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientAlphaShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBL
