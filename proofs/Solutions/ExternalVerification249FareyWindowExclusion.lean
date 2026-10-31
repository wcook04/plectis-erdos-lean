/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos257PeriodNoncollapse.CertificateKernel

/-!
# Source transport for the Farey-window totient-series exclusion in Erdős #249
-/

namespace Erdos249257.ExternalVerification249FareyWindowExclusion

theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053

theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053

end Erdos249257.ExternalVerification249FareyWindowExclusion
