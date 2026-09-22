/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band m

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsM
open scoped BigOperators
/-- A bound is dyadically dominated when every fixed rational denominator is eventually overwhelmed by the depth scale. Polynomial bounds have this property; the definition isolates exactly the growth input used below. Local copy of ErdosProblems.Erdos251.DyadicScaleDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ,
    2 * bound (N + r) * q < 2 ^ r
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- `x` lies in the affine class `-c` modulo `2^(r+1)`. Local copy of ErdosProblems.Erdos251.RatAffinePowTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)
/-- A rational that is the cast of an even integer. Local copy of ErdosProblems.Erdos251.RatEvenIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatEvenIntegral (x : ℚ) : Prop := ∃ k : ℤ, x = ((2 * k : ℤ) : ℚ)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The integer block accumulated through `h` dyadic tail steps beginning at index `N`. Recursively, this is `g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. Local copy of ErdosProblems.Erdos251.dyadicTailBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)
/-- The least common multiple of the positive integers seen so far. Local copy of ErdosProblems.Erdos251.lcmDiagonalSchedule, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- The digit sequence governing the fixed `h`-shift cocycle. Local copy of ErdosProblems.Erdos251.shiftDigit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
/-- States long251:xr:propagate from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.realTailShift_integral_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realTailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    ∀ k : ℕ, RealIntegral (realTailShift T h (N + k)) := by
  sorry
/-- States eq:affinecofinal, eq:affinecollapse, eq:dyadicscale from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.affine_circularity_bundle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
/-- States long251:res:lcmdiagonal from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_initial_iff_all_lcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsM
