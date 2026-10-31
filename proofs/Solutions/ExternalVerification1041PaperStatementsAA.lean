/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.PaperTrinomial
import ErdosProblems.Erdos1041.PaperTrinomialWholeR21

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCurveAssembly`, `ErdosProblems.Erdos1041.PaperTrinomial`,
`ErdosProblems.Erdos1041.PaperTrinomialWholeR21`.
-/

open Set
open scoped NNReal
open scoped ENNReal

namespace Erdos249257.ExternalVerification1041PaperStatementsAA

noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)

noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b

theorem complete_trinomial {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z₁ z₂ : ℂ} (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    Continuous (hub z₁ 0 z₂) ∧
    hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
    (∀ t ∈ Icc (0 : ℝ) 2,
      ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
    BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal = ‖z₁‖ + ‖z₂‖ ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  apply ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial <;> assumption

theorem all_degree_monic_trinomials_whole
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1) :
    (∀ z : ℂ, polynomialValue n m a b z = 0 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1) ∧
    ∀ z₁ z₂ : ℂ,
      polynomialValue n m a b z₁ = 0 →
      polynomialValue n m a b z₂ = 0 → z₁ ≠ z₂ →
      Continuous (hub z₁ 0 z₂) ∧
      hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
      (∀ t ∈ Icc (0 : ℝ) 2,
        ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
      BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal =
        ‖z₁‖ + ‖z₂‖ ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := @ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole n m hm hmn a b hroots

end Erdos249257.ExternalVerification1041PaperStatementsAA
