/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR7.ArithmeticAssemblies
import Solutions.PalomarCorpus.E249_07.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsH

theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := @ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square

end PalomarCorpus.E249.PaperStatementsH
