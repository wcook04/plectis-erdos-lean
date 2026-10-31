/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification68FactorialGapBounds
open Filter Topology
open scoped BigOperators

noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

theorem factorial_gap_gcd_exact
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
    let Q := n.descFactorial (n - m)
    g ∣ Q - 1 ∧ g ≤ Q - 1 ∧ Q - 1 < n ^ (n - m) := by
  sorry

theorem factorialGapSegment_log_sum_le_channelLCM_add_choose
    {D k : ℕ} (hkD : k < D) :
    (∑ n ∈ Finset.Ico (D + 1 - k) (D + 1),
      Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM D : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  sorry

end Erdos249257.ExternalVerification68FactorialGapBounds
end
