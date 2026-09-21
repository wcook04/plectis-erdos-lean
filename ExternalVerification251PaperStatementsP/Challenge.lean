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
`ErdosProblems.Erdos251.PaperFiniteCertificatesR7`,
`ErdosProblems.Erdos251.PrimeGapDyadicTail`, `ErdosProblems.Erdos251.RealPrimeGapTail`.
-/

open scoped BigOperators
open Finset

namespace Erdos249257.ExternalVerification251PaperStatementsP

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

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

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

/-- States long251:res:finite-smallpair from the long record for Erdős problem #251. Transported
from ErdosProblems.Erdos251.PaperR7.finite_small_pair in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem finite_small_pair :
    (-1 < realTailShift realPrimeGapTail 1 2 ∧
      realTailShift realPrimeGapTail 1 2 < 1) ∧
    (-1 < realTailShift realPrimeGapTail 1 3 ∧
      realTailShift realPrimeGapTail 1 3 < 1) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 2) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 3) ∧
    primeGap0 4 = 2 ∧ primeGap0 3 = 4 := by
  sorry

end Erdos249257.ExternalVerification251PaperStatementsP
