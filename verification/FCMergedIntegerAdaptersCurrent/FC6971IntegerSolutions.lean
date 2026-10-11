import FormalConjecturesAdapter

open scoped BigOperators

/- Receiving-pinned proof adapters; runtime verification pending. -/

namespace Erdos257

theorem erdos_257.variants.tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  exact Erdos249257.FormalConjecturesAdapter.erdos_257_variants_tsum_top

end Erdos257

#print axioms Erdos257.erdos_257.variants.tsum_top

namespace Erdos1049

theorem erdos_1049.variants.geq_2_integer :
     ∀ t : ℤ, t ≥ 2 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  exact Erdos249257.FormalConjecturesAdapter.erdos_1049_variants_geq_2_integer

end Erdos1049

#print axioms Erdos1049.erdos_1049.variants.geq_2_integer

namespace Erdos258

theorem erdos_258.variants.constant : True ↔ ∀ t ≥ (2 : ℕ),
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / t^(n + 1))) := by
  exact Erdos249257.FormalConjecturesAdapter.erdos_258_variants_constant

end Erdos258

#print axioms Erdos258.erdos_258.variants.constant
