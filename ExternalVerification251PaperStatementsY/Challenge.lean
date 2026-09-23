/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.NonconcentrationConsequencesR11`,
`ErdosProblems.Erdos251.NonconcentrationCoreR11`,
`ErdosProblems.Erdos251.PaperCompleteR21.TwoWindowSparsity`,
`ErdosProblems.Erdos251.PrimeGapDyadicTail`, `ErdosProblems.Erdos251.RealPrimeGapTail`.
-/

open scoped BigOperators
open Filter
open Topology
open Finset

namespace Erdos249257.ExternalVerification251PaperStatementsY

noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}

noncomputable def shift (T : ℕ → ℝ) (h N : ℕ) : ℝ := T (N + h) - T N

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))

/-- States long251:res:sparse from the long record for Erdős problem #251. Transported from
ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gap_equal_shift_zeroDensity (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := by
  sorry

/-- States long251:res:sparse from the long record for Erdős problem #251. Transported from
ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gap_two_window_sparse (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | 1 ≤ N ∧
        (-1 < shift realPrimeGapTail h N ∧ shift realPrimeGapTail h N < 1) ∧
        (-1 < shift realPrimeGapTail h (N + 1) ∧
          shift realPrimeGapTail h (N + 1) < 1) ∧
        (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ)} ∧
      ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)} := by
  sorry

end Erdos249257.ExternalVerification251PaperStatementsY
