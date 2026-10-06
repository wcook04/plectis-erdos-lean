/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.FirstHarmonicGap
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.FirstHarmonicGap`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint`.
-/

open Filter
open Finset

namespace Erdos249257.ExternalVerification249PaperStructuresU

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))

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

end Erdos249257.ExternalVerification249PaperStructuresU
