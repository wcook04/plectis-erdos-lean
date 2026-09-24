/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.TropicalCurvatureCarry
import ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss

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

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `VUSymbol` and its source `Erdos249257.TotientTailPeriodKiller.VUSymbol` carry the same
fields, so each converts into the other field by field. -/
def VUSymbol_transport_toSrc (x : VUSymbol) :
    Erdos249257.TotientTailPeriodKiller.VUSymbol :=
  ⟨x.valuation, x.unit⟩

/-- The inverse of `VUSymbol_transport_toSrc`. -/
def VUSymbol_transport_ofSrc (x : Erdos249257.TotientTailPeriodKiller.VUSymbol) :
    VUSymbol :=
  ⟨x.valuation, x.unit⟩

@[simp] theorem VUSymbol_transport_toSrc_valuation
    (x : VUSymbol) :
    (VUSymbol_transport_toSrc x).valuation = x.valuation := rfl

@[simp] theorem VUSymbol_transport_ofSrc_valuation
    (x : Erdos249257.TotientTailPeriodKiller.VUSymbol) :
    (VUSymbol_transport_ofSrc x).valuation = x.valuation := rfl

@[simp] theorem VUSymbol_transport_toSrc_unit
    (x : VUSymbol) :
    (VUSymbol_transport_toSrc x).unit = x.unit := rfl

@[simp] theorem VUSymbol_transport_ofSrc_unit
    (x : Erdos249257.TotientTailPeriodKiller.VUSymbol) :
    (VUSymbol_transport_ofSrc x).unit = x.unit := rfl

/-- A source orbit over the converted word is an orbit of the copied inductive `VUOrbit`
over the original word. The two inductives have the same constructors, and the conversion
keeps both fields, so each source step is a copied step (hand-written bridge: the
generator's inductive map does not reach an indexed family of propositions). -/
theorem VUOrbit_of_src_transport (u : ℕ) :
    ∀ (e : ℤ) (symbols : List VUSymbol) (states : List ℤ),
      Erdos249257.TotientTailPeriodKiller.VUOrbit u e
          (symbols.map VUSymbol_transport_toSrc) states →
        VUOrbit u e symbols states := by
  intro e symbols
  induction symbols generalizing e with
  | nil =>
      intro states h
      cases h
      exact VUOrbit.nil e
  | cons σ rest ih =>
      intro states h
      cases h with
      | cons _ c e' _ _ tail hcompat hstep htail =>
          exact VUOrbit.cons e c e' σ rest tail hcompat hstep (ih e' tail htail)

theorem fixed_precision_carry_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states := by
  obtain ⟨states, horbit, hbound⟩ :=
    ErdosProblems.Erdos249.PaperCompleteR21.fixed_precision_carry_completion u hu
      (symbols.map VUSymbol_transport_toSrc)
      (by
        intro σ hσ
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hσ
        exact hodd τ hτ)
      e
  exact ⟨states, VUOrbit_of_src_transport u e symbols states horbit,
    List.forall₂_map_left_iff.mp hbound⟩

end Erdos249257.ExternalVerification249PaperStructuresR
