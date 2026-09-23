/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.IncidenceQuotientHermitePade
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import Solutions.PalomarCorpus.E249_04.Statement

open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsK

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
            ↔ c = 0 := @ErdosProblems.Erdos249.PaperCompleteR21.b6_mobius_incidence_unimodular_and_injective N

end PalomarCorpus.E249.PaperStatementsK
