/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence
import ErdosProblems.Erdos243.PaperCompleteR20.TwoForbiddenWords
import ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections
import Solutions.PalomarCorpus.E243_01.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresAD
export PalomarCorpus.E243_01.Shared (LowerDensityAtLeast exceptionCount exceptionFinset)

theorem minus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 1 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile (-1) (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile (-1) n} (1 / 7) := @ErdosProblems.Erdos243.PaperCompleteR20.minus_one_forbidden_word a u v T hnum hden

theorem plus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 0 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile 1 (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile 1 n} (1 / 7) := @ErdosProblems.Erdos243.PaperCompleteR20.plus_one_forbidden_word a u v T hnum hden

end PalomarCorpus.E243.PaperStructuresAD
