import ExternalVerification.FC243CubicRate.Solution
import Solutions.PalomarCorpus.E243_06.PaperStatementsL

open Filter
open scoped Topology BigOperators

namespace Erdos243

/-- The prefix product of a positive integer sequence. -/
def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

/-- The increment of the prefix-product ratio, expressed using consecutive terms. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

/-- The truncated base-two iterated logarithm. -/
noncomputable def logLogTwo (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

theorem erdos_243.variants.slow_growth_product_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        logLogTwo ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    PalomarCorpus.E243.PaperStatementsL.productDefect a n ≤ (1 - δ) / (q : ℝ) *
      PalomarCorpus.E243.PaperStatementsL.recordLogLog
        ((PalomarCorpus.E243.PaperStatementsL.prefixProduct a n : ℝ) / (a n : ℝ)) at hslow
  exact PalomarCorpus.E243.PaperStatementsL.original_coordinate_slow_growth_defect
    a ha hpos p q hq hs hgrowth δ hδ hslow

theorem erdos_243.variants.cubic_rate (a : ℕ → ℕ)
    (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))) atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  exact ErdosProblems.Erdos243.FormalConjecturesAdapter.erdos_243_variants_cubic_rate a ha hpos hrate

#print axioms erdos_243.variants.slow_growth_product_defect
#print axioms erdos_243.variants.cubic_rate

end Erdos243
