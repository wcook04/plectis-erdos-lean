/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import Solutions.PalomarCorpus.E251_06.Statement

namespace PalomarCorpus.E251.LcmDiagonalCriterion
export PalomarCorpus.E251_06.Shared (RealDyadicTailRecurrence RealIntegral realTailShift)

noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬ RealIntegral (realTailShift T h N)

noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)

private theorem lcmDiagonalSchedule_eq_source (j : ℕ) :
    lcmDiagonalSchedule j = ErdosProblems.Erdos251.lcmDiagonalSchedule j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [lcmDiagonalSchedule,
        ErdosProblems.Erdos251.lcmDiagonalSchedule, ih]

theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) :=
  ErdosProblems.Erdos251.not_irrational_initial_iff_exists_integral_positive_tailShift
    hrec

theorem irrationalInitial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalNonintegralTailShifts hrec

theorem tailShiftIntegral_iff_orderOf_dvd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      orderOf (2 : ZMod (T N).den) ∣ h :=
  ErdosProblems.Erdos251.tailShift_integral_iff_orderOf_dvd hrec N h

theorem irrationalInitial_iff_nonintegral_on_schedule
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) :=
  ErdosProblems.Erdos251.irrational_initial_iff_nonintegral_on_schedule
    hrec s hpos hdvd hgrow

theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  simp only [lcmDiagonalSchedule_eq_source]
  exact ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral hrec

end PalomarCorpus.E251.LcmDiagonalCriterion
