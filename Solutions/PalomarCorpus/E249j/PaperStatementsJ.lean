/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.SignedQMomentObstruction
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import Solutions.PalomarCorpus.E249j.Statement

open scoped BigOperators
open Matrix
open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsJ

theorem b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half :
    mobiusMersenneTheta 2 = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := @ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half

end PalomarCorpus.E249.PaperStatementsJ
