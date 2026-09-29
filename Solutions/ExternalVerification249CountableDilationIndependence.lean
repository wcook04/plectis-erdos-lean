/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos249.FiniteDilationLinearIndependent

set_option autoImplicit false

namespace ExternalVerification249CountableDilationIndependence

theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        ∑' n : ℕ, ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1)) := by
  simpa only [ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue, Rat.cast_natCast] using
    ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB

end ExternalVerification249CountableDilationIndependence
