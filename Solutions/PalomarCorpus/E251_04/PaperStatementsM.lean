/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.AffineCylinderCollapse
import ErdosProblems.Erdos251.AffineShiftEscape
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.PaperCompleteR20.RealPropagation
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251_04.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsM
export PalomarCorpus.E251_04.Shared (DyadicTailRecurrence RatIntegral RealIntegral realTailShift tailShift)

noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)

theorem realTailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    ∀ k : ℕ, RealIntegral (realTailShift T h (N + k)) := @ErdosProblems.Erdos251.PaperCompleteR20.realTailShift_integral_add g T hrec h N hInt

theorem affine_circularity_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    (∀ h N r : ℕ,
      RatAffinePowTwo (tailShift T h (N + r))
        (dyadicTailBlock (shiftDigit g h) N r) r ↔
      RatEvenIntegral (tailShift T h N)) ∧
    (∀ h : ℕ,
      (∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) ∧
    (∀ (h : ℕ) (bound : ℕ → ℚ),
      (∀ N, |tailShift T h N| ≤ bound N) → DyadicScaleDominates bound →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ∀ z : ℤ,
        bound (N + r) <
          |(dyadicTailBlock (shiftDigit g h) N r : ℚ) - 2 ^ r * (z : ℚ)|) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos251.PaperR7.affine_circularity_bundle g T hrec

theorem irrational_initial_iff_all_lcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral g T hrec

end PalomarCorpus.E251.PaperStatementsM
