/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.HalfUpperResetCriticalBand
import ErdosProblems.Erdos257.PaperCompleteR21.DyadicBandAndTwoSidedBounds

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.HalfUpperResetCriticalBand`,
`ErdosProblems.Erdos257.PaperCompleteR21.DyadicBandAndTwoSidedBounds`.
-/

open Finset

namespace Erdos249257.ExternalVerification257PaperStatementsBE

noncomputable def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)

noncomputable def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)

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

end Erdos249257.ExternalVerification257PaperStatementsBE
