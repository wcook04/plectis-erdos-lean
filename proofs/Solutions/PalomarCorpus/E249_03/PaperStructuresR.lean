/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TropicalCurvatureCarry
import ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss
import Solutions.PalomarCorpus.E249_03.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresR

/-- The copied structure `VUSymbol` and its source `Erdos249257.TotientTailPeriodKiller.VUSymbol` carry the same
fields, so each converts into the other field by field. -/
noncomputable def VUSymbol_transport_toSrc (x : VUSymbol) :
    Erdos249257.TotientTailPeriodKiller.VUSymbol :=
  ⟨x.valuation, x.unit⟩

/-- The inverse of `VUSymbol_transport_toSrc`. -/
noncomputable def VUSymbol_transport_ofSrc (x : Erdos249257.TotientTailPeriodKiller.VUSymbol) :
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

end PalomarCorpus.E249.PaperStructuresR
