import Solutions.ExternalVerification249CountableDilationIndependence

namespace Erdos249

theorem erdos_249.variants.least_residue_dilation_independence
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        ∑' n : ℕ, ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1)) := by
  exact ExternalVerification249CountableDilationIndependence.linearIndependent_one_and_least_residue_values m B hm hB

#print axioms erdos_249.variants.least_residue_dilation_independence

end Erdos249
