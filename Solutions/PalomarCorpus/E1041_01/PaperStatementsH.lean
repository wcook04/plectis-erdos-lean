/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperTrinomial
import Solutions.PalomarCorpus.E1041_01.Statement

open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsH
export PalomarCorpus.E1041_01.Shared (polynomialValue)

theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1 := @ErdosProblems.Erdos1041.PaperTrinomial.all_spokes n m hm hmn a b hroots z hz t ht0 ht1

end PalomarCorpus.E1041.PaperStatementsH
