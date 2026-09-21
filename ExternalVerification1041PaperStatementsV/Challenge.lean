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
`ErdosProblems.Erdos1041.PaperCompleteR21.PrimitiveQuinticClosedDisc`,
`ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10`,
`ErdosProblems.Erdos1041.PaperPrimitivePath`.
-/

open Polynomial
open Set
open scoped BigOperators

namespace Erdos249257.ExternalVerification1041PaperStatementsV

noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)

noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c

/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041.
Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.tail_le_one_and_eq_iff_of_leading_zero in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1) := by
  sorry

/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041.
Transported from ErdosProblems.Erdos1041.PaperCompleteR21.tail_norm_of_leading_zero in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5 := by
  sorry

/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041.
Transported from ErdosProblems.Erdos1041.PaperCompleteR21.two_tails_closedDisc_of_ne_zero in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsV
