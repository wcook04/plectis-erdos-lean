/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import FormalConjecturesVariants

/-- The reciprocal-summable support theorem in the subtype notation used by
Formal Conjectures. The original indicator proof is retained unchanged. -/
theorem Erdos257.erdos_257.variants.summable_reciprocal_support_subtype
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  rw [tsum_subtype A (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1))]
  exact Erdos257.erdos_257.variants.summable_reciprocal_support b A hb hA
    ((summable_subtype_iff_indicator (s := A)
      (f := fun a : ℕ => (1 : ℝ) / (a : ℝ))).mp hsum)

#print axioms Erdos257.erdos_257.variants.summable_reciprocal_support_subtype
