/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR20.TwoNearestPolynomial`.
-/

open Finset
open Polynomial
open scoped BigOperators

namespace Erdos249257.ExternalVerification1041PaperStatementsB

/-- States the paper statement it is bound to from the short record for Erdős problem #1041.
Transported from
ErdosProblems.Erdos1041.PaperCompleteR20.exists_two_nearest_roots_of_polynomial_critical in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0) :
    ∃ i j : Fin n, i ≠ j ∧
      (∀ k, ‖c - z i‖ ≤ ‖c - z k‖) ∧
      (∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) ∧
      ‖c - z i‖ + ‖c - z j‖ < 2 := by
  sorry

/-- States the paper statement it is bound to from the short record for Erdős problem #1041.
Transported from
ErdosProblems.Erdos1041.PaperCompleteR20.two_nearest_roots_of_polynomial_critical in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, ‖c - z i‖ ≤ ‖c - z k‖)
    (hj : ∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) :
    ‖c - z i‖ + ‖c - z j‖ < 2 := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsB
