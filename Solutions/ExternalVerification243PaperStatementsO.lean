/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR7.Limits
import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR7.Limits`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter

namespace Erdos249257.ExternalVerification243PaperStatementsO

noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

theorem sparse_gcd_changes
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hlim : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N ↦
      (((Finset.range N).filter (fun j ↦
        Nat.gcd (C j) (D j) < Nat.gcd (C (j + 1)) (D (j + 1)))).card : ℝ) /
          (N : ℝ)) atTop (nhds 0) ∧
    (∀ B L : ℕ, ∃ n, B ≤ n ∧ ∀ j, j ≤ L →
      Nat.gcd (C (n + j)) (D (n + j)) = Nat.gcd (C n) (D n)) := @ErdosProblems.Erdos243.PaperCompleteR7.sparse_gcd_changes a C D E hCpos hC hD hE hlim

end Erdos249257.ExternalVerification243PaperStatementsO
