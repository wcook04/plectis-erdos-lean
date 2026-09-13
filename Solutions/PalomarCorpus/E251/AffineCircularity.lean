/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.AffineCylinderCollapse
import Solutions.PalomarCorpus.E251.Statement

namespace PalomarCorpus.E251.AffineCircularity
export PalomarCorpus.E251.Shared (DyadicTailRecurrence RatIntegral tailShift)

private theorem dyadicTailBlock_eq_source (a : ℕ → ℤ) (N r : ℕ) :
    dyadicTailBlock a N r = ErdosProblems.Erdos251.dyadicTailBlock a N r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [dyadicTailBlock, ErdosProblems.Erdos251.dyadicTailBlock, ih]

theorem adjacent_small_mismatch_iff_signed_two_window
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧
        -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧
        g (N + h + 1) ≠ g (N + 1)) ↔
      ((g (N + h + 1) - g (N + 1) = 2 ∧
          1 / 2 < tailShift T h N ∧ tailShift T h N < 1) ∨
        (g (N + h + 1) - g (N + 1) = -2 ∧
          -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) :=
  ErdosProblems.Erdos251.adjacent_small_mismatch_iff_signed_two_window
    hrec h N heven

theorem cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  simp only [dyadicTailBlock_eq_source]
  exact ErdosProblems.Erdos251.cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    hrec h hdiffEven

theorem cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (bound : ℕ → ℚ)
    (hbound : ∀ N, |tailShift T h N| ≤ bound N)
    (hscale : DyadicScaleDominates bound) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
      ∀ z : ℤ, bound (N + r) <
        |((dyadicTailBlock (shiftDigit g h) N r : ℤ) : ℚ) -
          2 ^ r * (z : ℚ)|) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  simp only [dyadicTailBlock_eq_source]
  exact ErdosProblems.Erdos251.cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    hrec h bound hbound hscale

end PalomarCorpus.E251.AffineCircularity
