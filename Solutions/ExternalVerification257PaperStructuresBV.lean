/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit`.
-/

open Filter
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresBV

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

noncomputable def listGreedyRemAfter : ℕ → List ℕ → ℕ → ℕ
  | 0, _, C => C
  | _ + 1, [], C => C
  | m + 1, w :: ws, C => listGreedyRemAfter m ws (if w ≤ C then C - w else C)

noncomputable def seamIntRem (s m : ℕ) : ℕ :=
  listGreedyRemAfter m (seamWeights s) (seamSubsetTarget s)

noncomputable def seamScaledTarget (s : ℕ) : ℝ :=
  (seamSubsetTarget s : ℝ) / (4 : ℝ) ^ s

noncomputable def seamScaledWeight (s d : ℕ) : ℝ :=
  (truncatedMersenneWeight s d : ℝ) / (4 : ℝ) ^ s

noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom` is the same function. -/
theorem seamWeightsFrom_transport_def : @seamWeightsFrom = @Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom := by
  first
  | (rfl; done)
  | (simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (ext x; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a; fun_induction seamWeightsFrom a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a; induction a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a b; fun_induction seamWeightsFrom a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; induction b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (funext a b c; fun_induction seamWeightsFrom a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, *]; done)
  | (funext a b c; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)
  | (simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeights` is the same function. -/
theorem seamWeights_transport_def : @seamWeights = @Erdos249257.HalfCylinderIntegerGreedy.seamWeights := by
  first
  | (rfl; done)
  | (simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (ext x; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a; fun_induction seamWeights a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a b; fun_induction seamWeights a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (funext a b c; fun_induction seamWeights a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)
  | (simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, seamWeightsFrom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter` is the same function. -/
theorem listGreedyRemAfter_transport_def : @listGreedyRemAfter = @ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter := by
  first
  | (rfl; done)
  | (simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold listGreedyRemAfter ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter; done)
  | (unfold listGreedyRemAfter ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (ext x; simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; fun_induction listGreedyRemAfter a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; fun_induction listGreedyRemAfter a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; fun_induction listGreedyRemAfter a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (simp [listGreedyRemAfter, ErdosProblems.Erdos257.PaperCompleteR21.listGreedyRemAfter, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem` is the same function. -/
theorem seamIntRem_transport_def : @seamIntRem = @ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem := by
  first
  | (rfl; done)
  | (simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamIntRem ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem; done)
  | (unfold seamIntRem ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (ext x; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a; fun_induction seamIntRem a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a; simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a b; fun_induction seamIntRem a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b; simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (funext a b c; fun_induction seamIntRem a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, *]; done)
  | (funext a b c; simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (simp [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def] <;> rfl; done)
  | (funext v1; unfold seamIntRem ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem <;> simp only [seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [seamIntRem, ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold seamIntRem ErdosProblems.Erdos257.PaperCompleteR21.seamIntRem <;> simp only [seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder` is the same function. -/
theorem tailGreedyRemainder_transport_def : @tailGreedyRemainder = @ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder := by
  first
  | (rfl; done)
  | (simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold tailGreedyRemainder ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder; done)
  | (unfold tailGreedyRemainder ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (ext x; simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a; fun_induction tailGreedyRemainder a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a; induction a <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a; induction a <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a; induction a <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a; simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a b; fun_induction tailGreedyRemainder a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b; simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (funext a b c; fun_induction tailGreedyRemainder a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def, *]; done)
  | (funext a b c; simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)
  | (simp [tailGreedyRemainder, ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, seamWeightsFrom_transport_def, seamWeights_transport_def, listGreedyRemAfter_transport_def, seamIntRem_transport_def]; done)

theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder s hs

end Erdos249257.ExternalVerification257PaperStructuresBV
