/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band g

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Finset

namespace PalomarCorpus.E243.PaperStatementsG
open Filter
open Finset
/-- The literal error in `C (n+1) / C n = 1 + l/n + ε_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.rateError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rateError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C (n + 1) / C n - (1 + l / (n : ℝ))
/-- `risingPow d x = x (x+1) ⋯ (x + d - 1)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.risingPow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingPow (d : ℕ) (x : ℝ) : ℝ := ∏ i ∈ Finset.range d, (x + (i : ℝ))
/-- States long243:eq:regularrate, long243:res:extraction from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem regular_rate_extraction {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ d : ℕ, 2 ≤ d ∧ l = (d : ℝ) ∧
      ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℝ) = (A : ℝ) * risingPow d (n : ℝ) + (B : ℝ) := by
  sorry
end PalomarCorpus.E243.PaperStatementsG
