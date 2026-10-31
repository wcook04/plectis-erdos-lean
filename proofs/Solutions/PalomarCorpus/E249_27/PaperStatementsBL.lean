/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.PivotAntiReconstruction
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.BinaryDigitChangeDensity
import Solutions.PalomarCorpus.E249_27.Statement

open scoped Classical
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBL
export PalomarCorpus.E249_27.Shared (totientAlphaShift totientTail)

theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h)) := @ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq h N

end PalomarCorpus.E249.PaperStatementsBL
