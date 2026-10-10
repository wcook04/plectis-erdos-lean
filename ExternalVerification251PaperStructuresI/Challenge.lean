/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Large denominator certificate for Erdős #251

Restates `res:cfexclusion` against Mathlib alone. The source theorem is
`ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both` at public paper commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf`.
The Solution transports its kernel proof of both actual prime series; the
250 finite prime-census chunks are checked by Lean's kernel, without an oracle.
This interface is prepared pending fresh release compilation and Comparator replay.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStructuresI

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- The printed denominator floor for both actual series (`res:cfexclusion`). -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b ∨
      (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b := by
  sorry

end Erdos249257.ExternalVerification251PaperStructuresI
