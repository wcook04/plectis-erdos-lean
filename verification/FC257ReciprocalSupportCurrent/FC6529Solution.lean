import Solutions.FC257Subtype

namespace Erdos257

theorem erdos_257.variants.summable_reciprocal_support
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  exact Erdos257.erdos_257.variants.summable_reciprocal_support_subtype b A hb hA hsum

end Erdos257

#print axioms Erdos257.erdos_257.variants.summable_reciprocal_support
