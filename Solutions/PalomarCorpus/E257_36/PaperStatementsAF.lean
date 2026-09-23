/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DyadicPrefixCompression
import Erdos249257.SublogDivisorCoverage
import Solutions.PalomarCorpus.E257_36.Statement

open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAF

noncomputable def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r

noncomputable def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)

noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := @Erdos249257.card_divisors_le_divisorSubpowerConst_mul_rpow n k hk

theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n := @Erdos249257.card_divisors_pow_le_divisorSubpowerConst_pow_mul n k hn hk

theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0 := @Erdos249257.divInt_le_nextDyadic_iff_excess_nonpos p n L hL

theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D := @Erdos249257.dyadicResidual_denominator_sandwich p r c D hDpos hDodd hrD hle

end PalomarCorpus.E257.PaperStatementsAF
