/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.AffineCylinderCollapse
import ErdosProblems.Erdos251.AffineShiftEscape
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.PaperCompleteR20.RealPropagation
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.AffineCylinderCollapse`, `ErdosProblems.Erdos251.AffineShiftEscape`,
`ErdosProblems.Erdos251.OrderLatticeDiagonal`,
`ErdosProblems.Erdos251.PaperCompleteR20.RealPropagation`,
`ErdosProblems.Erdos251.PaperCoreR7`, `ErdosProblems.Erdos251.PrimeGapDyadicTail`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251PaperStatementsM

noncomputable def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ,
    2 * bound (N + r) * q < 2 ^ r

noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)

noncomputable def RatEvenIntegral (x : ℚ) : Prop := ∃ k : ℤ, x = ((2 * k : ℤ) : ℚ)

noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)

noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)

noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

noncomputable def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n

noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

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

end Erdos249257.ExternalVerification251PaperStatementsM
