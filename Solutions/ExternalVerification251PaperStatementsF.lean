/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7
import ErdosProblems.Erdos251.PaperNonconcentrationR7

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperFiniteCertificatesR7`,
`ErdosProblems.Erdos251.PaperNonconcentrationR7`.
-/

open scoped BigOperators
open Finset

namespace Erdos249257.ExternalVerification251PaperStatementsF

noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}

theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589 := @ErdosProblems.Erdos251.PaperR7.denominator_floor_decimal

theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b := @ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability a b E ha hE

end Erdos249257.ExternalVerification251PaperStatementsF
