/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification251ExactDenominatorFloors
open Filter Topology
open scoped BigOperators

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) := by
  simpa only [prime0, primeGap0, primeDyadicTerm, primeGapDyadicTerm, ErdosProblems.Erdos251.prime0, ErdosProblems.Erdos251.primeGap0, ErdosProblems.Erdos251.primeDyadicTerm, ErdosProblems.Erdos251.primeGapDyadicTerm] using
    ErdosProblems.Erdos251.PaperR7.denominator_floor_both a b hb

end Erdos249257.ExternalVerification251ExactDenominatorFloors
end
