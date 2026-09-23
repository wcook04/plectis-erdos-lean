/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperCompleteR20.ExactDenominator`,
`ErdosProblems.Erdos251.PrimeGapDyadicTail`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsJ

noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

/-- States res:escape-irrational from the short record for Erdős problem #251. Transported from
ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_orbit_exact_den_and_shift
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T)
    (q : ℚ) (hq0 : T 0 = q) (s d : ℕ) (hq : q.den = 2^s*d) (hd : Odd d)
    (N h : ℕ) (hh : 0 < h) :
    (∃ v : ℚ, T N = v ∧ v.den = 2^(s-N)*d) ∧
    (RealIntegral (realTailShift T h N) ↔ s ≤ N ∧ d ∣ 2^h-1) := by
  sorry

end Erdos249257.ExternalVerification251PaperStatementsJ
