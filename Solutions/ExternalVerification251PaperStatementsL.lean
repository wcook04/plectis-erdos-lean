/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.FreePairReduction`, `ErdosProblems.Erdos251.PaperCoreR7`,
`ErdosProblems.Erdos251.PrimeGapDyadicTail`, `ErdosProblems.Erdos251.RealPrimeGapTail`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsL

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))

theorem actual_free_pair_criterion :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral realPrimeGapTail := @ErdosProblems.Erdos251.PaperR7.actual_free_pair_criterion

end Erdos249257.ExternalVerification251PaperStatementsL
