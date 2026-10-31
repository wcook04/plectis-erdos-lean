/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification249RankOneDenominator
open Filter Topology
open scoped BigOperators

open ArithmeticFunction
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  sorry

end Erdos249257.ExternalVerification249RankOneDenominator
end
