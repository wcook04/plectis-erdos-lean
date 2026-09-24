/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
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

namespace Erdos249257.ExternalVerification257PaperStructuresCA

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

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

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

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.greedyMersenneRemainder` is the same function. -/
theorem greedyMersenneRemainder_transport_def : @greedyMersenneRemainder = @Erdos249257.greedyMersenneRemainder := by
  first
  | (rfl; done)
  | (simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (with_unfolding_all rfl; done)
  | (unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder; done)
  | (unfold greedyMersenneRemainder Erdos249257.greedyMersenneRemainder <;> simp only [Erdos249257.greedyMersenneRemainder, *]; done)
  | (ext x; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a; fun_induction greedyMersenneRemainder a <;> simp only [Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a; induction a <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a b; fun_induction greedyMersenneRemainder a b <;> simp only [Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; induction b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; induction a generalizing b <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; induction b generalizing a <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (funext a b c; fun_induction greedyMersenneRemainder a b c <;> simp only [Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder, *]; done)
  | (funext a b c; simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (simp [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder] <;> rfl; done)
  | (funext v1 v2; simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.greedyMersenneSupport` is the same function. -/
theorem greedyMersenneSupport_transport_def : @greedyMersenneSupport = @Erdos249257.greedyMersenneSupport := by
  first
  | (rfl; done)
  | (simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold greedyMersenneSupport Erdos249257.greedyMersenneSupport; done)
  | (unfold greedyMersenneSupport Erdos249257.greedyMersenneSupport <;> simp only [Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (ext x; simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a; fun_induction greedyMersenneSupport a <;> simp only [Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a; induction a <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a; simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a b; fun_induction greedyMersenneSupport a b <;> simp only [Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b; simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (funext a b c; fun_induction greedyMersenneSupport a b c <;> simp only [Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def, *]; done)
  | (funext a b c; simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (simp [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport, greedyMersenneRemainder_transport_def] <;> rfl; done)
  | (funext v1; unfold greedyMersenneSupport Erdos249257.greedyMersenneSupport <;> simp only [greedyMersenneRemainder_transport_def] <;> rfl; done)

theorem IsStraddlePrefix.half_agrees_greedy
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport (1 / 2 : ℝ)) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_agrees_greedy u d (IsStraddlePrefix_transport_bridge.mp hu)

end Erdos249257.ExternalVerification257PaperStructuresCA
