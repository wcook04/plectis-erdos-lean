/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `a25cb360bef8dd818dde14b5fb752244304af354` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TropicalCurvatureCarry`,
`ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss`.
-/

namespace Erdos249257.ExternalVerification249PaperStructuresR

structure VUSymbol where
  valuation : ℕ
  unit : ℤ

noncomputable def VUCompatible (u : ℕ) (σ : VUSymbol) (c : ℤ) : Prop :=
  Odd σ.unit ∧
    ∃ z : ℤ,
      c = (2 : ℤ) ^ σ.valuation * (σ.unit + (2 : ℤ) ^ u * z)

inductive VUOrbit (u : ℕ) : ℤ → List VUSymbol → List ℤ → Prop
  | nil (e : ℤ) : VUOrbit u e [] []
  | cons (e c e' : ℤ) (σ : VUSymbol) (symbols : List VUSymbol)
      (states : List ℤ) (hcompat : VUCompatible u σ c)
      (hstep : e' = 2 * e + c) (htail : VUOrbit u e' symbols states) :
      VUOrbit u e (σ :: symbols) (e' :: states)

noncomputable def vuRadius (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u - 1)

/-- States prop:b5 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.fixed_precision_carry_completion in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fixed_precision_carry_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states := by
  sorry

end Erdos249257.ExternalVerification249PaperStructuresR
