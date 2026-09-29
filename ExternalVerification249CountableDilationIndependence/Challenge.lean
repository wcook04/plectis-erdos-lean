/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

set_option autoImplicit false

namespace ExternalVerification249CountableDilationIndependence

/-- For each modulus m >= 3 and integer base B >= 2, the constant 1 and all positive-dilation least-residue totient values are rationally linearly independent. This bounded-residue theorem does not decide the unreduced Erdős 249 series. -/
theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        ∑' n : ℕ, ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1)) := by
  sorry

end ExternalVerification249CountableDilationIndependence
