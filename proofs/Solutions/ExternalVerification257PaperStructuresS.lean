/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator
import ErdosProblems.Erdos257.PaperCompleteR21.OneSidedCertificateHierarchy

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GreedyAchievementSet`, `Erdos249257.HalfCutLocator`,
`ErdosProblems.Erdos257.PaperCompleteR21.OneSidedCertificateHierarchy`.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresS

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied predicate bundle `IsStraddlePrefix` and its source `Erdos249257.IsStraddlePrefix` have the
same fields, so they are the same proposition. This equivalence is the fidelity
evidence for every statement below that mentions it. -/
theorem IsStraddlePrefix_transport_bridge {t : ℝ} {u : Finset ℕ} {d : ℕ} :
    IsStraddlePrefix t u d ↔ Erdos249257.IsStraddlePrefix t u d := by
  first
  | (exact ⟨fun hx => ⟨hx.mem_bounds, hx.value_le, hx.le_value_add_tail⟩, fun hx => ⟨hx.mem_bounds, hx.value_le, hx.le_value_add_tail⟩⟩; done)
  | (constructor <;> (intro hx; constructor <;> simp_all); done)

theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet) := by
  simpa only [IsStraddlePrefix_transport_bridge] using @ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sidedness

end Erdos249257.ExternalVerification257PaperStructuresS
