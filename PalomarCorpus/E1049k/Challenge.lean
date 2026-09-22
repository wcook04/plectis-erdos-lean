/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band k

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsK
open scoped BigOperators
/-- Natural-valued magnitude of the forcing term in the cleared recurrence. Local copy of ErdosProblems.Erdos1049.rationalBaseForcingNat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
/-- States long1049:res:chargeceilings from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.charge_ceilings in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem charge_ceilings :
    (∀ N : ℤ, 0 < N →
      41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N : ℤ, 2 ≤ N →
      41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 0 < N → E ≤ N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 2 ≤ N → E ≤ 2 * N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) := by
  sorry
/-- States long1049:res:forcing, res:forcing from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.forcing_term in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forcing_term (B : ℕ) (c : ℕ → ℕ) (N : ℕ) :
    (∀ s : ℕ, 2 ≤ s → 1 ≤ B → 1 ≤ c (N + 1) →
      2 ^ (N + 1) ≤ rationalBaseForcingNat s B c N) ∧
      rationalBaseForcingNat 1 B c N = B * c (N + 1) := by
  sorry
/-- States long1049:res:powerbracket from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.power_bracket in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem power_bracket :
    (2 : ℕ) ^ 64 < 3 ^ 41 ∧ 3 ^ 41 < 2 ^ 65 ∧
      (41 : ℝ) / 65 < Real.log 2 / Real.log 3 ∧
      Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := by
  sorry
/-- States long1049:res:scalar from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.scalar_margin in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scalar_margin {C0 C1 : ℝ} (hC1 : 0 < C1)
    (hs : C0 ≤ 0 ∨ 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < 0 ∧
      (0 < C0 → 2 * C0 ≤ C1 →
        C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsK
