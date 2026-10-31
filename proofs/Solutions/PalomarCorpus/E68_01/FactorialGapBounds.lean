/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import Solutions.PalomarCorpus.E68_01.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E68.FactorialGapBounds
export PalomarCorpus.E68_01.Shared (channelLCM)

theorem factorial_gap_gcd_exact
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
    let Q := n.descFactorial (n - m)
    g ∣ Q - 1 ∧ g ≤ Q - 1 ∧ Q - 1 < n ^ (n - m) := by
  simpa only [channelLCM, Erdos68.channelLCM] using
    Erdos68.factorial_gap_gcd_exact hm hmn

theorem factorialGapSegment_log_sum_le_channelLCM_add_choose
    {D k : ℕ} (hkD : k < D) :
    (∑ n ∈ Finset.Ico (D + 1 - k) (D + 1),
      Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM D : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  simpa only [channelLCM, Erdos68.channelLCM] using
    Erdos68.factorialGapSegment_log_sum_le_channelLCM_add_choose hkD

end PalomarCorpus.E68.FactorialGapBounds
end
