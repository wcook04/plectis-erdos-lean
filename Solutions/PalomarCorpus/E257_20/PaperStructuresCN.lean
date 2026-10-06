/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator
import Solutions.PalomarCorpus.E257_20.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCN
export PalomarCorpus.E257_20.Shared (mersenneWeight positiveMersenneSupportValue)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

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

theorem divInt_mem_nextMersenneDyadicSliver_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    (1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ∧
        Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1)) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p) := by
  simp only [IsStraddlePrefix_transport_bridge]
  exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL

theorem positiveMersenneSupportValue_insert {F : Finset ℕ} {a : ℕ}
    (ha : a ∉ F) :
    positiveMersenneSupportValue (↑(insert a F) : Set ℕ)
      = mersenneWeight a + positiveMersenneSupportValue (↑F : Set ℕ) := by
  simp only [IsStraddlePrefix_transport_bridge]
  exact @Erdos249257.positiveMersenneSupportValue_insert F a ha

end PalomarCorpus.E257.PaperStructuresCN
