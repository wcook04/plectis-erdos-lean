/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.PaperCompleteR21.BinaryDigitChangeDensity`.
-/

open scoped Classical

namespace Erdos249257.ExternalVerification249PaperStatementsAM

noncomputable def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j

noncomputable def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|

noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2

noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)

noncomputable def quarterFarPhaseCount (h X : ℕ) : ℕ :=
  ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h)).card

noncomputable def quarterFarPhaseProportion (h X : ℕ) : ℝ := (quarterFarPhaseCount h X : ℝ) / (X : ℝ)

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.cos_nonpos_of_quarterFarFromInt in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cos_nonpos_of_quarterFarFromInt {x : ℝ} (hx : QuarterFarFromInt x) :
    Real.cos (2 * Real.pi * x) ≤ 0 := by
  sorry

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totientSeries_of_digitChange_count
    (hnd : ∀ h : ℕ, 1 ≤ h → NotDyadicRational (totientAlphaShift h))
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1)
              ≠ binaryDigitAt (totientAlphaShift h) (N + 2)).card : ℕ) : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totientSeries_of_quarterFarPhase_count
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤ (quarterFarPhaseCount h X : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totientSeries_of_quarterFarPhase_proportion
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) ≤ quarterFarPhaseProportion h X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_binaryDigitAt_change in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem quarterFarFromInt_iff_binaryDigitAt_change {α : ℝ} (hnd : NotDyadicRational α) (N : ℕ) :
    QuarterFarFromInt ((2 : ℝ) ^ N * α) ↔ binaryDigitAt α (N + 1) ≠ binaryDigitAt α (N + 2) := by
  sorry

/-- States cor:digitform from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_floor_bounds in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem quarterFarFromInt_iff_floor_bounds (x : ℝ) :
    QuarterFarFromInt x ↔ (1 / 4 : ℝ) ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 3 / 4 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAM
