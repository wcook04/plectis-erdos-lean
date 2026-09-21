/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band f

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Set

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
/-- Completely explicit constant for the fixed-`k` divisor bound. Local copy of Erdos249257.divisorSubpowerConst, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)
/-- Numerator left after subtracting a reduced finite prefix `r / D` from a dyadic rational `p / 2^c`. The transport theorem below assumes the subtraction is nonnegative, so natural subtraction is exact. Local copy of Erdos249257.dyadicResidualNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r
/-- The displayed residual rational before its remaining power-of-two cancellation is normalized by `Rat`. Local copy of Erdos249257.dyadicResidualRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)
/-- For a displayed residual `p / (2L)`, the integer numerator of its excess above the next dyadic point `2^-(n+1)`. Indeed, `p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`. Keeping `E` integral makes the unresolved skipped-branch comparison an exact Diophantine inequality rather than a real-valued phase estimate. Local copy of Erdos249257.nextDyadicExcessIntNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)
/-- States record:257rig-i4b from the long record for Erdős problem #257. Transported from Erdos249257.card_divisors_le_divisorSubpowerConst_mul_rpow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  sorry
/-- States record:257rig-i4b from the long record for Erdős problem #257. Transported from Erdos249257.card_divisors_pow_le_divisorSubpowerConst_pow_mul in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n := by
  sorry
/-- States lem:dyadic-excess-reformulation from the long record for Erdős problem #257. Transported from Erdos249257.divInt_le_nextDyadic_iff_excess_nonpos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0 := by
  sorry
/-- States lem:denominator-sandwich from the long record for Erdős problem #257. Transported from Erdos249257.dyadicResidual_denominator_sandwich in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D := by
  sorry
end PalomarCorpus.E257.PaperStatementsAF
