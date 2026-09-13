/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.WeightedSupportLimits
import Solutions.PalomarCorpus.E257.Statement

open Filter Topology

namespace PalomarCorpus.E257.DyadicObservationSummability

noncomputable section

theorem supportObservationMass_eq :
    supportObservationMass = ErdosProblems.Erdos257.supportObservationMass :=
  rfl

theorem weightedObservationTerm_eq :
    weightedObservationTerm = ErdosProblems.Erdos257.weightedObservationTerm :=
  rfl

theorem dyadic_supportObservationMass_sum_le (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (J : Finset ℕ) (Q : ℕ) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j * supportObservationMass A α (Q * 2 ^ j)) ≤
      2 * (Q : ℝ) * ∑' a : ℕ, weightedObservationTerm A α a := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq, weightedObservationTerm_eq]
  exact ErdosProblems.Erdos257.dyadic_supportObservationMass_sum_le A α hα hs' J Q

theorem summable_dyadic_supportObservationMass (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j *
      supportObservationMass A α (Q * 2 ^ j)) := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq]
  exact ErdosProblems.Erdos257.summable_dyadic_supportObservationMass A α hα hs' Q

theorem tendsto_dyadic_supportObservationMass_mean (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M) atTop (nhds 0) := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq]
  exact ErdosProblems.Erdos257.tendsto_dyadic_supportObservationMass_mean A α hα hs' Q

end

end PalomarCorpus.E257.DyadicObservationSummability
