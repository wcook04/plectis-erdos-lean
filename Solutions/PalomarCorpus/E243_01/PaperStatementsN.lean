/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDefect
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDifferenceLimits
import ErdosProblems.Erdos243.PaperCompleteR21.RegularRateExtraction
import Solutions.PalomarCorpus.E243_01.Statement

open Filter
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsN

theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ) := @ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic C hpos hratio

end PalomarCorpus.E243.PaperStatementsN
