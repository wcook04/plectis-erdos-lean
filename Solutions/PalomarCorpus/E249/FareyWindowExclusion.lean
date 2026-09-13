/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.CertificateKernel
import Solutions.PalomarCorpus.E249.Statement

namespace PalomarCorpus.E249.FareyWindowExclusion

theorem farey_int_exclusion :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053

theorem farey_rat_exclusion :
    ∀ p : ℚ, p.den ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053

end PalomarCorpus.E249.FareyWindowExclusion
