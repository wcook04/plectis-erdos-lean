/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251h.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsH

theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos251.PaperR7.real_block_identity g T hrec N h

end PalomarCorpus.E251.PaperStatementsH
