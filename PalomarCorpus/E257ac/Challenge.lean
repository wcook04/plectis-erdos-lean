/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band c

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Finset

namespace PalomarCorpus.E257.PaperStatementsAC
open Finset
/-- `j` indexes the smallest power `2^(d-j+1)` that is still at least `E`. The final disjunction handles the last index, where there is no next power in the band family. Local copy of Erdos249257.HalfUpperResetCriticalBand.CriticalDyadicBandIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)
/-- Avoidance of every width-`2(d+j)` interval immediately below the dyadic power indexed by `j`. Local copy of Erdos249257.HalfUpperResetCriticalBand.DyadicBandEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
/-- Average at the T positive multiples of L. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.progressionMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)
/-- The literal modular atom requested in mandate 1a. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.kernelWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)
/-- The finite positive frame potential. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.framePotential, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def framePotential (F : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ F, kernelWeight 2 a N
/-- The indicator of the paper's event `{U_F > 1}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.exceedInd, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0
/-- The paper's `ℙ_ℓ(U_F > 1)`: uniform sampling of `N = ℓ m` over one period `Q/ℓ` of `m ↦ U_F(ℓ m)`. For `ℓ ∣ Q` the sampled points `ℓ, 2ℓ, …, Q` are a complete set of representatives of the multiples of `ℓ` modulo `Q`, so this is `ℙ(U_F(N) > 1 | ℓ ∣ N)` for `N` uniform modulo `Q`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.condExceedProb, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)
/-- The paper's modulus `Q = lcm F`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.frameLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def frameLcm (F : Finset ℕ) : ℕ := F.lcm id
/-- The paper's divisor-incidence count `f_F(n) = #{a ∈ F : a ∣ n}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.incidenceCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def incidenceCount (F : Finset ℕ) (n : ℕ) : ℕ := (F.filter (fun a => a ∣ n)).card
/-- Cost of a finitely supported nonnegative divisor majorant. Local copy of ErdosProblems.Erdos257.divisorMajorantCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d
/-- The costs of the admissible positive logarithmic divisor majorants of `(F, t)`: the feasible set of the paper's programme (display 9.185). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.logMajorantCosts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def logMajorantCosts (F : Finset ℕ) (t : ℝ) : Set ℝ :=
  {K : ℝ | ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧
    (∀ s ∈ (frameLcm F).divisors,
        Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) ∧
    K = divisorMajorantCost (frameLcm F).divisors c}
/-- The paper's `κ₁(F;t)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.kappaOne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kappaOne (F : Finset ℕ) (t : ℝ) : ℝ := sInf (logMajorantCosts F t)
/-- Average the progression averages over R ≤ j < R+M, T=2^j. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)
/-- States thm:critical-dyadic-band from the long record for Erdős problem #257. Transported from Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicBandEscape_iff_exists_critical
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := by
  sorry
/-- States thm:critical-dyadic-band from the long record for Erdős problem #257. Transported from Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_criticalDyadicBandIndex
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    ∃ j : ℕ, CriticalDyadicBandIndex d E j := by
  sorry
/-- States thm:257-logarithmic-counterexample from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F) := by
  sorry
/-- States prop:257-logarithmic-initial-interval from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t := by
  sorry
/-- States thm:257-logarithmic-counterexample from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_dyadic_kappaOne_constant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t := by
  sorry
end PalomarCorpus.E257.PaperStatementsAC
