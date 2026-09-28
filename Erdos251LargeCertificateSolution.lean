/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.PaperLargeCertificateR7

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification251LargeDenominatorFloor

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- The paper's finite denominator exclusion for either dyadic series.
This is compatible with rationality and does not decide Erdős Problem 251. -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b ∨
      (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b := by
  exact ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both a b hb hS

end Erdos249257.ExternalVerification251LargeDenominatorFloor
end
