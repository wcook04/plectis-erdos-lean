/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCutLocator
import Solutions.PalomarCorpus.E257_26.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCN
export PalomarCorpus.E257_26.Shared (mersenneWeightRat nextDyadicExcessIntNumerator)

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
  | (simpa only [IsStraddlePrefix, mersenneTail, mersenneWeight, mersenneWeightRat, nextDyadicExcessIntNumerator, positiveMersenneSupportValue] using Erdos249257.IsStraddlePrefix.half_strict; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d hu; done)
  | (exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.IsStraddlePrefix.half_strict u d (IsStraddlePrefix_transport_bridge.mp hu); done)

theorem divInt_mem_nextMersenneDyadicSliver_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    (1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ∧
        Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1)) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p) := by
  first
  | (simp only [IsStraddlePrefix_transport_bridge]
      exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (set_option smartUnfolding false in
      exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (apply Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess <;> assumption; done)
  | (simpa only [IsStraddlePrefix, mersenneTail, mersenneWeight, mersenneWeightRat, nextDyadicExcessIntNumerator, positiveMersenneSupportValue] using Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)
  | (with_unfolding_all exact @Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess p n L hL; done)

theorem positiveMersenneSupportValue_insert {F : Finset ℕ} {a : ℕ}
    (ha : a ∉ F) :
    positiveMersenneSupportValue (↑(insert a F) : Set ℕ)
      = mersenneWeight a + positiveMersenneSupportValue (↑F : Set ℕ) := by
  first
  | (simp only [IsStraddlePrefix_transport_bridge]
      exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (simp only [← IsStraddlePrefix_transport_bridge] at *
      simpa only [IsStraddlePrefix_transport_bridge] using @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (set_option smartUnfolding false in
      exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (apply Erdos249257.positiveMersenneSupportValue_insert <;> assumption; done)
  | (simpa only [IsStraddlePrefix, mersenneTail, mersenneWeight, mersenneWeightRat, nextDyadicExcessIntNumerator, positiveMersenneSupportValue] using Erdos249257.positiveMersenneSupportValue_insert; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)
  | (with_unfolding_all exact @Erdos249257.positiveMersenneSupportValue_insert F a ha; done)

end PalomarCorpus.E257.PaperStructuresCN
