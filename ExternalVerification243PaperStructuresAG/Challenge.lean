/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisationDedekind`.
-/

open NumberField
open Polynomial

namespace Erdos249257.ExternalVerification243PaperStructuresAG

/-- States long243:res:squarespec from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem squareSpecialisation_holds :
    ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
      Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
      ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
      G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
      J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
      (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
          (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
          (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
            IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
      ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
        β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresAG
