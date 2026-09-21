/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band m

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped Classical

namespace PalomarCorpus.E249.PaperStatementsAM
open scoped Classical
/-- `x` is nondyadic. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.NotDyadicRational, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j
/-- `‖x‖_{ℝ/ℤ} ≥ 1/4`, written as: every integer is at distance at least `1/4` from `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.QuarterFarFromInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|
/-- The `k`-th binary digit of `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.binaryDigitAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2
/-- `α_h = (2^h - 1) S`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientAlphaShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
/-- The number of `N ∈ [X, 2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseCount (h X : ℕ) : ℕ :=
  ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h)).card
/-- `ρ_h(X)`: the proportion of `N ∈ [X,2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.quarterFarPhaseProportion, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarterFarPhaseProportion (h X : ℕ) : ℝ := (quarterFarPhaseCount h X : ℝ) / (X : ℝ)
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cos_nonpos_of_quarterFarFromInt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cos_nonpos_of_quarterFarFromInt {x : ℝ} (hx : QuarterFarFromInt x) :
    Real.cos (2 * Real.pi * x) ≤ 0 := by
  sorry
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_of_digitChange_count
    (hnd : ∀ h : ℕ, 1 ≤ h → NotDyadicRational (totientAlphaShift h))
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1)
              ≠ binaryDigitAt (totientAlphaShift h) (N + 2)).card : ℕ) : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_of_quarterFarPhase_count
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤ (quarterFarPhaseCount h X : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_of_quarterFarPhase_proportion
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) ≤ quarterFarPhaseProportion h X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_binaryDigitAt_change in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem quarterFarFromInt_iff_binaryDigitAt_change {α : ℝ} (hnd : NotDyadicRational α) (N : ℕ) :
    QuarterFarFromInt ((2 : ℝ) ^ N * α) ↔ binaryDigitAt α (N + 1) ≠ binaryDigitAt α (N + 2) := by
  sorry
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_floor_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem quarterFarFromInt_iff_floor_bounds (x : ℝ) :
    QuarterFarFromInt x ↔ (1 / 4 : ℝ) ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 3 / 4 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAM
