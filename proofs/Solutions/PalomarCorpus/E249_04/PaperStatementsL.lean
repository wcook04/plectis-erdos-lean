/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientMahlerDefect
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import Solutions.PalomarCorpus.E249_04.Statement

open Module
open Matrix

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsL

theorem b6_retained_dyadic_sections_independent (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
      ∧ LinearIndependent ℚ (canonicalTotientKernelFamily e) := @ErdosProblems.Erdos249.PaperCompleteR21.b6_retained_dyadic_sections_independent e

end PalomarCorpus.E249.PaperStatementsL
