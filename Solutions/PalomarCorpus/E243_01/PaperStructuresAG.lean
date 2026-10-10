/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisationDedekind
import Solutions.PalomarCorpus.E243_01.Statement

open NumberField
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresAG

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
  first
  | exact @ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
    done
  | apply ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds <;> assumption
    done
  | simpa using ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
    done
  | with_unfolding_all exact @ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
    done

end PalomarCorpus.E243.PaperStructuresAG
