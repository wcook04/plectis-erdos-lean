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
`ErdosProblems.Erdos251.PaperCoreR7`, `ErdosProblems.Erdos251.PrimeGapDyadicTail`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsH

noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

/-- States long251:res:block from the long record for Erdős problem #251. Transported from
ErdosProblems.Erdos251.PaperR7.real_block_identity in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  sorry

end Erdos249257.ExternalVerification251PaperStatementsH
