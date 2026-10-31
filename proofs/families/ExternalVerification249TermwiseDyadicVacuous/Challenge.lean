/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the termwise dyadic-window vacuity in Erdős #249

The termwise hypothesis `2^t ∣ φ(N+t)` never beats the size budget
`v·(N+t+2)`. The termwise form of the dyadic window therefore excludes no
denominator. This is a no-go, not a solution of Erdős #249.
-/

namespace Erdos249257.ExternalVerification249TermwiseDyadicVacuous

set_option linter.unusedVariables false

/-- The termwise dyadic window excludes no denominator: `2^t ≤ φ(N+t) < N+t`. -/
theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) := by
  sorry

end Erdos249257.ExternalVerification249TermwiseDyadicVacuous
