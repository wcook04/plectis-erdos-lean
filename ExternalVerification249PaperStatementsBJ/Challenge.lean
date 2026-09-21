/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TotientCarryKernelRigidity`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.DyadicSectionBasisAndRationalCarry`.
-/

open Module
open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsBJ

noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.rationalValue_integral_carry_and_rank_floor in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem rationalValue_integral_carry_and_rank_floor
    {v : ℕ} (hv : 0 < v) {p : ℤ}
    (hvS : (v : ℝ) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ)) :
    ∃ u : ℕ → ℤ,
      (∀ N : ℕ, (u N : ℝ) = (v : ℝ) * totientTail N) ∧
      (∀ N : ℕ, u (N + 1) = 2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ)) ∧
      (∀ N : ℕ, 0 ≤ u N ∧ u N ≤ (v : ℤ) * ((N : ℤ) + 2)) ∧
      (∀ e : ℕ, 2 ^ e - 1 ≤
        Module.finrank ℚ
          (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBJ
