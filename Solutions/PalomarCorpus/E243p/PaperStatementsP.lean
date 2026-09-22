/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldCoordinates
import ErdosProblems.Erdos243.PaperCompleteR20.ScaleTwelve
import Solutions.PalomarCorpus.E243p.Statement

open Polynomial
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsP

theorem scale_twelve_of_square_in_rootField
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hsquare : ∃ β : L,
      β ∈ IntermediateField.adjoin ℚ ({α} : Set L) ∧
      β ^ 2 = α ^ 2 - 1) :
    m = 12 := @ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField L inferInstance inferInstance m c hm hc α hirr hroot hsquare

end PalomarCorpus.E243.PaperStatementsP
