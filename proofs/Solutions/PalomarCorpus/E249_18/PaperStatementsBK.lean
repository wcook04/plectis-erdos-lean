/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.ActualForeignResidueProjection
import Erdos249257.FullTargetPrimeAdjunctionNoGo
import Erdos249257.RadicalMobiusShadow
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection
import Solutions.PalomarCorpus.E249_18.Statement

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBK
export PalomarCorpus.E249_18.Shared (baseMobiusShadow diagonalCoefficient foreignComplementBound foreignResidueKernel mersenne mobiusNumerator numericMobiusShadow projectedForeignDefect residueIncrement residueOffset scaleExplicitShadow scaleExplicitShadowRat squarefreeKernel)

theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound :
      |totientTail (2 * H) - totientTail H -
        (scaleExplicitShadow H + projectedForeignDefect H D)| ≤
        foreignComplementBound H D)
    (hsep : ∀ z : ℤ,
      foreignComplementBound H D <
        |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    totientTail (2 * H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation H D hbound hsep

end PalomarCorpus.E249.PaperStatementsBK
