/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.FirstHarmonicGap
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint
import Solutions.PalomarCorpus.E249_33.Statement

open Filter
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresU
export PalomarCorpus.E249_33.Shared (windowDiscrepancy)

theorem irrational_totient_series_of_support_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧ T.Nonempty ∧ (∀ N ∈ T, A ≤ N ∧ N < 2 * X) ∧
      (∑ N ∈ T, windowFirstCos h N L) ≤ (9 / 10 : ℝ) * T.card) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  first
  | (exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap hgap; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap hgap; done)
  | (apply ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap <;> assumption; done)
  | (simpa only [windowDiscrepancy, windowFirstCos] using ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap hgap; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap hgap; done)

end PalomarCorpus.E249.PaperStructuresU
