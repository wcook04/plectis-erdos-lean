import ErdosProblems.Erdos249.PaperCompleteR7.RationalObservableClassification

namespace Erdos249

theorem erdos_249.variants.rational_dyadic_observable
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  exact ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.rational_zmod_observable_iff hk f


end Erdos249

#print axioms Erdos249.erdos_249.variants.rational_dyadic_observable
