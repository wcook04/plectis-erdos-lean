/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band v

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Set
open scoped BigOperators

namespace PalomarCorpus.E1041.PaperStatementsV
open Polynomial
open Set
open scoped BigOperators
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.tail_le_one_and_eq_iff_of_leading_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1) := by
  sorry
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.tail_norm_of_leading_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5 := by
  sorry
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.two_tails_closedDisc_of_ne_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsV
