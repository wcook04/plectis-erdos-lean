/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band k

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open ArithmeticFunction

namespace PalomarCorpus.E249.PaperStatementsK
open ArithmeticFunction
/-- Coefficient of `q^n` in the Möbius companion `M_mu(q^r)`. Local copy of IncidenceQuotientHermitePade.mobiusCompanionCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCompanionCoeff (r n : ℕ) : ℤ :=
  if r ∣ n then moebius (n / r) else 0
/-- The finite Möbius-incidence matrix on the positive jet coordinates `q, q^2, ..., q^N`. Columns are companion jets. Local copy of IncidenceQuotientHermitePade.incidenceMobiusMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def incidenceMobiusMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => mobiusCompanionCoeff (j.val + 1) (i.val + 1)
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_mobius_incidence_unimodular_and_injective in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_mobius_incidence_unimodular_and_injective (N : ℕ) :
    (∀ i j : Fin N,
        incidenceMobiusMatrix N i j =
          if (j : ℕ) + 1 ∣ (i : ℕ) + 1 then
            ArithmeticFunction.moebius (((i : ℕ) + 1) / ((j : ℕ) + 1)) else 0)
      ∧ (incidenceMobiusMatrix N).BlockTriangular
          OrderDual.toDual
      ∧ (∀ i : Fin N,
          incidenceMobiusMatrix N i i = 1)
      ∧ Matrix.det (incidenceMobiusMatrix N) = 1
      ∧ Function.Injective
          (incidenceMobiusMatrix N).mulVec
      ∧ ∀ c : Fin N → ℤ,
          (incidenceMobiusMatrix N).mulVec c = 0
            ↔ c = 0 := by
  sorry
end PalomarCorpus.E249.PaperStatementsK
