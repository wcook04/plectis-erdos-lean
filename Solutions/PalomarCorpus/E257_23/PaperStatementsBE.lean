/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfUpperResetCriticalBand
import ErdosProblems.Erdos257.PaperCompleteR21.DyadicBandAndTwoSidedBounds
import Solutions.PalomarCorpus.E257_23.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsBE

theorem paper_critical_dyadic_band_index_eq_top_of_le_two {d E j : ℕ}
    (hE : E ≤ 2) (hj : CriticalDyadicBandIndex d E j) :
    j = d := @ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_eq_top_of_le_two d E j hE hj

theorem paper_critical_dyadic_band_index_unique {d E : ℕ}
    (hE : E ≤ 2 ^ (d + 1)) :
    ∃! j : ℕ, CriticalDyadicBandIndex d E j := @ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_unique d E hE

theorem paper_critical_dyadic_boundary_is_smallest {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    E ≤ 2 ^ (d - j + 1) ∧
      ∀ i : ℕ, i ≤ d → E ≤ 2 ^ (d - i + 1) →
        (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d - i + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_boundary_is_smallest d E j hj

theorem paper_dyadic_band_escape_iff_single_test {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    DyadicBandEscape d E ↔ E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_band_escape_iff_single_test d E j hj

end PalomarCorpus.E257.PaperStatementsBE
