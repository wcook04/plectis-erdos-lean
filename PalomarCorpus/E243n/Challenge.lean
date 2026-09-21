/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band n

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Finset

namespace PalomarCorpus.E243.PaperStatementsN
open Filter
open Finset
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.cubicRatioError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))
/-- The rising cubic used in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR20.risingCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)
/-- States long243:eq:regularrate, long243:res:extraction from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ) := by
  sorry
end PalomarCorpus.E243.PaperStatementsN
