/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band h

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Set

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
/-- A public function spelling exactly the trinomial in both papers. Local copy of ErdosProblems.Erdos1041.PaperTrinomial.polynomialValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b
/-- States res:trinomial-all-degree from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomial.all_spokes in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsH
