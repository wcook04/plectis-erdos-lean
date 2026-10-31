/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 12.1 to 12.2: the doubling identity; the full-block exponential-sum estimate

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open scoped Classical
open scoped Nat

namespace PalomarCorpus.E249_27.Shared
/-- `α_h = (2^h - 1) S`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientAlphaShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_27.Shared

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.doublingMap_iterate_apply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem doublingMap_iterate_apply (α : ℝ) (N : ℕ) :
    (fun x : ℝ => 2 * x)^[N] α = 2 ^ N * α := by
  sorry
/-- States prop:transfer from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_of_block_cosine_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))))
        ≤ (89 / 100 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_27.Shared (totientTail)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orbit_tail_diff_eq (h N : ℕ) :
    totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := by
  sorry
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_firstChar_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orbit_tail_diff_firstChar_eq (h N : ℕ) :
    Complex.exp
        (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
        (((2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) * Complex.I) := by
  sorry
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_fract_eq_doubling_orbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orbit_tail_diff_fract_eq_doubling_orbit (h N : ℕ) :
    Int.fract (totientTail (N + h) - totientTail N)
      = Int.fract
          ((fun x : ℝ => 2 * x)^[N]
            (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) := by
  sorry
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_sub_scaled_is_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orbit_tail_diff_sub_scaled_is_int (h N : ℕ) :
    ∃ z : ℤ,
      totientTail (N + h) - totientTail N
          - (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        = (z : ℝ) := by
  sorry
/-- States lem:orbit from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_recurrence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orbit_tail_recurrence (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAM
open scoped Classical
export PalomarCorpus.E249_27.Shared (totientAlphaShift)
/-- `x` is nondyadic. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.NotDyadicRational, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j
/-- `‖x‖_{ℝ/ℤ} ≥ 1/4`, written as: every integer is at distance at least `1/4` from `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.QuarterFarFromInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|
/-- The `k`-th binary digit of `x`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.binaryDigitAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2
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

namespace PalomarCorpus.E249.PaperStatementsBL
open scoped Classical
open Finset
export PalomarCorpus.E249_27.Shared (totientAlphaShift totientTail)
/-- First additive character of the infinite tail difference. Local copy of Erdos249257.TotientTailPeriodKiller.tailOrbitFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)
/-- States cor:digitform from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBL

namespace PalomarCorpus.E249.PaperStatementsAN
open Finset
open scoped Nat
/-- The paper's comparison coefficients: `c(n) = 1` when `n = k!` for some `k ≥ 1`, and `c(n) = 0` otherwise. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacCoef, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacCoef (n : ℕ) : ℤ :=
  @ite ℤ (∃ k : ℕ, 1 ≤ k ∧ n = k !) (Classical.propDecidable _) 1 0
/-- `β = ∑_{n ≥ 1} c(n)/2ⁿ` (the `n = 0` term vanishes since `k! ≥ 1`). Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacBeta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacBeta : ℝ := ∑' n : ℕ, (lacCoef n : ℝ) / 2 ^ n
/-- The paper's window discrepancy `D(h,N,L)` with the totient replaced by the comparison coefficients `c`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (lacCoef (N + h + 1 + j) - lacCoef (N + 1 + j)) * 2 ^ (L - 1 - j)
/-- The angle of the paper's `E(h,N,L)` for the comparison coefficients. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi * (((lacDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))
/-- The paper's `E(h,N,L) = e((D mod 2^L)/2^L)` for the comparison coefficients. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lacFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lacFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((lacFirstAngle h N L : ℂ) * Complex.I)
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_lacBeta : Irrational lacBeta := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
  sorry
/-- States thm:lacunary from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := by
  sorry
end PalomarCorpus.E249.PaperStatementsAN
