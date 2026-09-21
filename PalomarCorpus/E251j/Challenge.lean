/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band j

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsJ
open scoped BigOperators
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- States res:escape-irrational from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_orbit_exact_den_and_shift
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T)
    (q : ℚ) (hq0 : T 0 = q) (s d : ℕ) (hq : q.den = 2^s*d) (hd : Odd d)
    (N h : ℕ) (hh : 0 < h) :
    (∃ v : ℚ, T N = v ∧ v.den = 2^(s-N)*d) ∧
    (RealIntegral (realTailShift T h N) ↔ s ≤ N ∧ d ∣ 2^h-1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsJ
