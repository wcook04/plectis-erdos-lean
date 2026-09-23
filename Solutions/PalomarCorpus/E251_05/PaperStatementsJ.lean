/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCompleteR20.ExactDenominator
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251_05.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsJ
export PalomarCorpus.E251_05.Shared (RealDyadicTailRecurrence)

theorem real_orbit_exact_den_and_shift
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T)
    (q : ℚ) (hq0 : T 0 = q) (s d : ℕ) (hq : q.den = 2^s*d) (hd : Odd d)
    (N h : ℕ) (hh : 0 < h) :
    (∃ v : ℚ, T N = v ∧ v.den = 2^(s-N)*d) ∧
    (RealIntegral (realTailShift T h N) ↔ s ≤ N ∧ d ∣ 2^h-1) := @ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift g T hrec q hq0 s d hq hd N h hh

end PalomarCorpus.E251.PaperStatementsJ
