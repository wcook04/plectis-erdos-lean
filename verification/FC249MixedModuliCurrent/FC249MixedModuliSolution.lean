import ErdosProblems.Erdos249.FiniteDilationMixedModuli

open scoped BigOperators

namespace Erdos249

theorem erdos_249.variants.rational_mixed_dyadic_observables
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ) (q₀ : ℚ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (q₀ : ℝ) + (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  exact ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff
    D k f B q₀ hB hpos hk

#print axioms erdos_249.variants.rational_mixed_dyadic_observables

end Erdos249
