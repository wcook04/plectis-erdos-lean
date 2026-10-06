/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GreedyAchievementSet`, `Erdos249257.HalfCutLocator`.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace Erdos249257.ExternalVerification257PaperStructuresCH

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

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

theorem IsStraddlePrefix.half_strict {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    positiveMersenneSupportValue (↑u : Set ℕ) < 1 / 2 ∧
      (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
        + mersenneTail d := @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu)

end Erdos249257.ExternalVerification257PaperStructuresCH
