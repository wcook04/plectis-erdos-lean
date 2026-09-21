/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.ProductDefectThresholds
import Solutions.PalomarCorpus.E243f.Statement

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsF

theorem original_coordinate_strict_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (r : ℝ) (hr : r < 1)
    (hlimsup : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := @ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_strict_one a ha hpos p q hq hs hgrowth r hr hlimsup

end PalomarCorpus.E243.PaperStatementsF
