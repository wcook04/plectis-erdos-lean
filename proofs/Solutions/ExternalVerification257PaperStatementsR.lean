/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import Erdos249257.GreedyAchievementSet
import ErdosProblems.Erdos257.PaperCompleteR21.MobiusSignAndFiniteCertificates

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `Erdos249257.GreedyAchievementSet`,
`ErdosProblems.Erdos257.PaperCompleteR21.MobiusSignAndFiniteCertificates`.
-/

open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsR

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def mersenneTailUpperRat (n lookahead : ℕ) : ℚ :=
  (∑ k ∈ Finset.range lookahead, mersenneWeightRat (n + k + 1))
    + 2 * mersenneWeightRat (n + lookahead + 1)

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

noncomputable def CertifiedGreedyMersenneDeath
    (x : ℚ) (level lookahead : ℕ) : Prop :=
  mersenneTailUpperRat level lookahead
    ≤ greedyMersenneRemainderRat x level

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

theorem paper_finite_support_and_onesided_certificate :
    (∀ A : Set ℕ, A.Finite → 0 ∉ A → erdosSupportSeries 2 A ≠ (1 : ℝ) / 2) ∧
      (∀ F : Finset ℕ, 0 ∉ F → Odd (finiteErdosSum F 2).den) ∧
      (∀ n : ℕ, 1 ≤ n → Odd (2 ^ n - 1)) ∧
      ((1 : ℚ) / 2).den = 2 ∧ Even ((1 : ℚ) / 2).den ∧
      (∀ (x : ℚ) (level lookahead : ℕ),
        CertifiedGreedyMersenneDeath x level lookahead →
          ((x : ℚ) : ℝ) ∉ mersenneAchievementSet) ∧
      CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 ∧
      (3 / 4 : ℝ) ∉ mersenneAchievementSet ∧
      (∀ A : Set ℕ, 0 ∉ A → erdosSupportSeries 2 A = (1 : ℝ) / 2 → A.Infinite) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_and_onesided_certificate

end Erdos249257.ExternalVerification257PaperStatementsR
