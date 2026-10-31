/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Farey-window totient-series exclusion in Erdős #249

The two theorems exclude every integer ratio `a/d` and every rational `p`
whose denominator is at most `79639646646701375323355774875831053` as a
value of `∑ φ(n)/2ⁿ`. This is a finite exclusion, not irrationality of the
series. Erdős #249 remains open.
-/

namespace Erdos249257.ExternalVerification249FareyWindowExclusion

theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by
  sorry

theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry

end Erdos249257.ExternalVerification249FareyWindowExclusion
