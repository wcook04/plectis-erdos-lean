/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.PaperTailBoundsR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.RealPrimeGapTail

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperTailBoundsR7`, `ErdosProblems.Erdos251.PrimeGapDyadicTail`,
`ErdosProblems.Erdos251.RealPrimeGapTail`.
-/

open Filter
open Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsO

noncomputable def quarticTailPolynomial (x : ℝ) : ℝ :=
  x ^ 4 + 8 * x ^ 3 + 36 * x ^ 2 + 104 * x + 150

noncomputable def explicitRemainder (h N L : ℕ) : ℝ :=
  1250 / 2 ^ L * (quarticTailPolynomial ((N : ℝ) + h + L + 2) +
    quarticTailPolynomial ((N : ℝ) + L + 2))

noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N)) := @ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate h N L

end Erdos249257.ExternalVerification251PaperStatementsO
