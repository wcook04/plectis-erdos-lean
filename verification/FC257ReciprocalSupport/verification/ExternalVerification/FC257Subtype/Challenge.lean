/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent statement-only challenge. The official verifier protects this
statement and its trusted dependencies before compiling the solution. -/

theorem Erdos257.erdos_257.variants.summable_reciprocal_support_subtype
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  sorry
