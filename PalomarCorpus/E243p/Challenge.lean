/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band p

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsP
open Polynomial
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η
/-- States long243:res:scaletwelve from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
    m = 12 := by
  sorry
end PalomarCorpus.E243.PaperStatementsP
