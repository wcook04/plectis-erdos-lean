/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269f

Every non-theorem declaration of `PalomarCorpus/E269f/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsF
open scoped BigOperators
/-- A positive `p`-power lies strictly inside the dyadic block `(2^a, 2^(a+1))`. Endpoints are excluded because the dyadic jump itself is the distinguished terminal factor of the compressed block. Local copy of ErdosProblems.Erdos269.DyadicInternalPower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- The integer-power condition defining the paper's first clearing index. Local copy of ErdosProblems.Erdos269.PaperR13.ClearingCondition, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a
/-- The paper's elementary bound `a_D = u+1+2v+3w` satisfies all three integer-power thresholds. Local copy of ErdosProblems.Erdos269.PaperR13.clearingCondition_sufficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearingCondition_sufficient (u v w : ℕ) :
    ClearingCondition u v w (u + 1 + 2 * v + 3 * w) := by
  let aD := u + 1 + 2 * v + 3 * w
  have h2 : 2 ^ (u + 1) ≤ 2 ^ aD :=
    Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega)
  have h3four : 3 ^ v ≤ 4 ^ v := Nat.pow_le_pow_left (by norm_num) v
  have h4two : 4 ^ v = 2 ^ (2 * v) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : 3 ^ v ≤ 2 ^ aD := by
    rw [h4two] at h3four
    exact h3four.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  have h5eight : 5 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
  have h8two : 8 ^ w = 2 ^ (3 * w) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h5 : 5 ^ w ≤ 2 ^ aD := by
    rw [h8two] at h5eight
    exact h5eight.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  exact ⟨by omega, h2, h3, h5⟩
/-- The first positive scale satisfying the three integer-power comparisons. Local copy of ErdosProblems.Erdos269.PaperR13.firstClearingIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def firstClearingIndex (u v w : ℕ) : ℕ := by
  classical
  exact Nat.find ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩
/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding `x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. Local copy of ErdosProblems.Erdos269.threePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. Local copy of ErdosProblems.Erdos269.smooth3Val, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- Strict `{p,q,r}`-smooth exponent prefix. The ambient exponent box of side `x` is deliberately redundant; it gives a finite, integer-only carrier for the strict inequality used by the returned floor-sum formula. Local copy of ErdosProblems.Erdos269.strictSmoothExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- Exact shell between two strict cutoffs. Local copy of ErdosProblems.Erdos269.strictSmoothShell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The actual `{2,3,5}`-smooth exponent points in the half-open dyadic shell `[2^a,2^(a+1))`. Local copy of ErdosProblems.Erdos269.dyadicSmoothShell235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- Literal reciprocal running-height mass of one half-open dyadic shell. Local copy of ErdosProblems.Erdos269.dyadicShellMassQ235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- Rational mass of the smooth window `[start, start + count)` of shells. Local copy of ErdosProblems.Erdos269.dyadicSmoothWindowMassQ235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
/-- Half-height normalizer at scale `a`: the coefficient of the normalized tail state and the clearing denominator of the smooth prefix. Local copy of ErdosProblems.Erdos269.heightNormalizer235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The rational representative of the paper state `X_a`, written from the value `N / D` and the finite rational prefix below scale `a`. Local copy of ErdosProblems.Erdos269.PaperR13.rationalTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))
/-- Multiplicative base accumulated across a local window. Local copy of ErdosProblems.Erdos269.windowBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len
/-- The exact radix of the dyadic block after compressing all internal `3`- and `5`-power jumps. Each internal channel contributes its prime once, and the terminal dyadic jump contributes the factor `2`. Local copy of ErdosProblems.Erdos269.dyadicBlockBase235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- Local copy of ErdosProblems.Erdos269.PaperR7.actualWindowBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev actualWindowBase (lo len : ℕ) : ℤ :=
  windowBase (fun a => (dyadicBlockBase235 a : ℤ)) lo len
end PalomarCorpus.E269.PaperStatementsF
