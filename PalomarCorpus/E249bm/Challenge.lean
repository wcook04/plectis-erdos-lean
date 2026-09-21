/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band m

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open ArithmeticFunction
open scoped BigOperators
open Finset

namespace PalomarCorpus.E249.PaperStatementsBM
open ArithmeticFunction
open scoped BigOperators
open Finset
/-- The quotient of the first multiple of `d` strictly above `N`. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1
/-- The least strictly positive shift from `N` to a multiple of `d` when `d > 0`. At a divisor of `N` it is `d`, rather than zero. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBM
