/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence`,
`ErdosProblems.Erdos243.PaperCompleteR20.TwoForbiddenWords`,
`ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections`.
-/

namespace Erdos249257.ExternalVerification243PaperStructuresAD

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

noncomputable def LowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (d - ε) * (X : ℝ) ≤ (exceptionCount E X : ℝ)

noncomputable def cubicTwelveProfile (c : ℤ) (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) + c

noncomputable instance instFactPrimeOfNatNat_erdosProblems : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- States long243:res:modseven from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR20.minus_one_forbidden_word in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem minus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 1 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile (-1) (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile (-1) n} (1 / 7) := by
  sorry

/-- States long243:res:modseven from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR20.plus_one_forbidden_word in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem plus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 0 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile 1 (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile 1 n} (1 / 7) := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresAD
