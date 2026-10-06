/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator
import Solutions.PalomarCorpus.E257_20.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCH
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)

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
        + mersenneTail d := by
  first
  | (exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (have hsrc := @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu)
      simp only [IsStraddlePrefix_transport_bridge] at hsrc ⊢
      exact hsrc; done)
  | (simp only [IsStraddlePrefix_transport_bridge]
      exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (set_option smartUnfolding false in
      exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (apply Erdos249257.IsStraddlePrefix.half_strict <;> assumption; done)
  | (simpa only [IsStraddlePrefix, mersenneTail, mersenneWeight, positiveMersenneSupportValue] using Erdos249257.IsStraddlePrefix.half_strict; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)

end PalomarCorpus.E257.PaperStructuresCH
