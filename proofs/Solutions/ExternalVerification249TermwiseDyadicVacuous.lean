/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity

/-!
# Source transport for the termwise dyadic-window vacuity in Erdős #249
-/

namespace Erdos249257.ExternalVerification249TermwiseDyadicVacuous

set_option linter.unusedVariables false

theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) :=
  ErdosProblems.Erdos249.termwise_dyadic_window_vacuous ht hNt hv hdvd

end Erdos249257.ExternalVerification249TermwiseDyadicVacuous
