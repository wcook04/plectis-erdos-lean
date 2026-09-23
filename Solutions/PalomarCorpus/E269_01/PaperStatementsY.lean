/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperCompleteR21.TwoPrimeSums
import ErdosProblems.Erdos269.PaperR7AnalyticInterfaces
import Solutions.PalomarCorpus.E269_01.Statement

open Polynomial
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsY
export PalomarCorpus.E269_01.Shared (BugeaudLaurentTranscendence heckeMahlerSeries)

theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (twoPrimeHeckeValue p q) := @ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue hBL p q hp hq hpq

end PalomarCorpus.E269.PaperStatementsY
