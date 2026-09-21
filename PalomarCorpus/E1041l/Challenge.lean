/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band l

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex

namespace PalomarCorpus.E1041.PaperStatementsL
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsL
