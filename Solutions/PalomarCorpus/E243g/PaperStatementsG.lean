/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.RegularRateExtraction
import Solutions.PalomarCorpus.E243g.Statement

open Filter
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsG

theorem regular_rate_extraction {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ d : ℕ, 2 ≤ d ∧ l = (d : ℝ) ∧
      ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℝ) = (A : ℝ) * risingPow d (n : ℝ) + (B : ℝ) := @ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction l hl C hpos hratio

end PalomarCorpus.E243.PaperStatementsG
