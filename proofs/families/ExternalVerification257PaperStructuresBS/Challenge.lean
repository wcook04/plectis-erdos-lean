/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos257.CoverIndependentPeriodicMean`,
`ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleAssembly`,
`ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBound`,
`ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBoundPaperForm`,
`ErdosProblems.Erdos257.PaperCompleteR21.FiniteFamilyCoverCost`,
`ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval`,
`ErdosProblems.Erdos257.PaperCompleteR8.FiniteMeans`,
`ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence`,
`ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget`.
-/

open Finset

namespace Erdos249257.ExternalVerification257PaperStructuresBS

noncomputable def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)

noncomputable def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)

noncomputable def framePotential (F : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ F, kernelWeight 2 a N

noncomputable def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0

noncomputable def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)

noncomputable def finiteCoverCost (N : ℕ) (weight exponent : ℕ → ℝ) (coefficient : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
      / ((2 : ℝ) ^ exponent j - 1)

noncomputable def finiteLogCoverCosts (A : Set ℕ) : Set ℝ :=
  {K : ℝ | ∃ (N : ℕ) (frame : ℕ → Finset ℕ) (weight exponent : ℕ → ℝ)
      (coefficient : ℕ → ℕ → ℝ),
    (∀ j, 0 ∉ frame j) ∧
    (∀ j, j < N → 0 < weight j) ∧
    (∑ j ∈ Finset.range N, weight j = 1) ∧
    (∀ j, 0 < exponent j ∧ exponent j ≤ 1) ∧
    (∀ j d, 0 < d → 0 ≤ coefficient j d) ∧
    (∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))) ∧
    (∀ a ∈ A, ∃ j, j < N ∧ a ∈ frame j) ∧
    (∀ j n, 0 < n →
      (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j
        ≤ ∑ d ∈ n.divisors, coefficient j d) ∧
    K = finiteCoverCost N weight exponent coefficient}

noncomputable def frameLcm (F : Finset ℕ) : ℕ := F.lcm id

noncomputable def incidenceCount (F : Finset ℕ) (n : ℕ) : ℕ := (F.filter (fun a => a ∣ n)).card

noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d

noncomputable def logMajorantCosts (F : Finset ℕ) (t : ℝ) : Set ℝ :=
  {K : ℝ | ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧
    (∀ s ∈ (frameLcm F).divisors,
        Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) ∧
    K = divisorMajorantCost (frameLcm F).divisors c}

noncomputable def kappaOne (F : Finset ℕ) (t : ℝ) : ℝ := sInf (logMajorantCosts F t)

structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

noncomputable def LogBudgetCover.cost {A : Set ℕ} (C : LogBudgetCover A) : ℝ :=
  ∑' j, (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
    (C.weight j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)

noncomputable def admissibleLogCoverCosts (A : Set ℕ) : Set ℝ :=
  Set.range (fun C : LogBudgetCover A => C.cost)

noncomputable def paperCoverCost (A : Set ℕ) : ℝ :=
  sInf (admissibleLogCoverCosts A ∪ finiteLogCoverCosts A)

/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record
for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) := by
  sorry

/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record
for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_paperCoverCost_kappaOne_constant in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1 := by
  sorry

/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record
for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.sup_condExceedProb_le_paperCoverCost in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBS
