/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfUpperResetCriticalBand
import ErdosProblems.Erdos257.CoverIndependentPeriodicMean
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleAssembly
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBound
import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval
import ErdosProblems.Erdos257.PaperCompleteR8.FiniteMeans
import ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence
import Solutions.PalomarCorpus.E257_20.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAC

noncomputable def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)

noncomputable def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)

noncomputable def framePotential (F : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ F, kernelWeight 2 a N

noncomputable def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0

noncomputable def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)

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

noncomputable def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)

theorem dyadicBandEscape_iff_exists_critical
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := @Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical d E hE

theorem exists_criticalDyadicBandIndex
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    ∃ j : ℕ, CriticalDyadicBandIndex d E j := @Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex d E hE

theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F) := by
  apply ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample <;> assumption

theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t := @ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval F hFne hF X hX t ht ht1

theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t := @ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_dyadic_kappaOne_constant

end PalomarCorpus.E257.PaperStatementsAC
