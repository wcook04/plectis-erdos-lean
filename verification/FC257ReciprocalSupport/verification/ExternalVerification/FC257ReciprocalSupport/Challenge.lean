/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent statement-only Challenge. The holes below are trusted targets,
never source proof evidence. Comparator must compile the original Solution
only after protecting this Challenge and its Mathlib dependency closure. -/

theorem Erdos257.erdos_257.variants.summable_reciprocal_support
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)))) :
    Irrational (∑' a : ℕ,
      Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a) := by sorry
