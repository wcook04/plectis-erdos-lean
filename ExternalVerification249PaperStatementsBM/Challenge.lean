/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TotientShiftedMobiusPulse`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion`.
-/

open ArithmeticFunction
open scoped BigOperators
open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsBM

noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1

noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBM
