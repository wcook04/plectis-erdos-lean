/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification251PrimeGapNonperiodicity
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

theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  sorry

end Erdos249257.ExternalVerification251PrimeGapNonperiodicity
end
