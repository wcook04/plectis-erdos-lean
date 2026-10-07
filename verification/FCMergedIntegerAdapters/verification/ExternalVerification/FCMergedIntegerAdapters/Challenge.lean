/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent statement-only Challenge. The holes below are trusted targets,
never source proof evidence. Comparator must compile the original Solution
only after protecting this Challenge and its Mathlib dependency closure. -/

theorem Erdos249257.FormalConjecturesAdapter.erdos_257_variants_tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by sorry

theorem Erdos249257.FormalConjecturesAdapter.erdos_1049_variants_geq_2_integer :
    ∀ t : ℤ, t ≥ 2 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by sorry

theorem Erdos249257.FormalConjecturesAdapter.erdos_258_variants_constant : True ↔ ∀ t ≥ (2 : ℕ),
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / t^(n + 1))) := by sorry
