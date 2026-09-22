/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerCertificatesT64
import Erdos249257.LcmFactorIdealPulseObstruction
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCertificateBatch
import ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts
import Solutions.PalomarCorpus.E249i.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsI

theorem historical_table_and_complete_band :
    (∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)) ∧
    (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band

theorem sixteen_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 → r.den ∣ 2 ^ 14 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificates_and_exclusions

theorem small_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 8 → r.den ∣ 2 ^ 12 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR20.small_certificates_and_exclusions

theorem b6_synthetic_sequence_prescribed_differences {t : ℕ} (ht : 3 ≤ t) :
    (∀ k : ℕ, k ∈ lcmAnchorStates t →
        lcmAnchorPulseState t k = -(Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ k : ℕ, k ∉ lcmAnchorStates t → lcmAnchorPulseState t k = 0)
      ∧ (∀ q : ℕ, 2 ≤ q → q < t →
          (q - 1) * periodLcm t ∈ lcmAnchorStates t)
      ∧ (∀ i : ℕ, lcmAnchorPulseLetter t i =
          2 * lcmAnchorPulseState t i - lcmAnchorPulseState t (i + 1))
      ∧ ∀ q : ℕ, 2 ≤ q → q < t →
          lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = (Nat.totient (periodLcm t) : ℤ)
            ∧ lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = deltaTotient (periodLcm t) (q * periodLcm t) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_sequence_prescribed_differences t ht

theorem b6_synthetic_shift_combinations_same_form
    (t : ℕ) (terms : List (ℕ × ℤ)) :
    (∀ i : ℕ,
        lcmAnchorShiftPolynomialState t terms i =
          shiftLinearCombination terms (lcmAnchorPulseState t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            shiftLinearCombination terms (lcmAnchorPulseLetter t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            2 * lcmAnchorShiftPolynomialState t terms i -
              lcmAnchorShiftPolynomialState t terms (i + 1))
      ∧ (∀ n L : ℕ,
          dyadicClearedPrefix (lcmAnchorShiftPolynomialLetter t terms) n L =
            (2 : ℤ) ^ L * lcmAnchorShiftPolynomialState t terms n -
              lcmAnchorShiftPolynomialState t terms (n + L))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialState t terms i| ≤
          shiftLinearWeight terms * (Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialLetter t terms i| ≤
          shiftLinearWeight terms * (2 * (Nat.totient (periodLcm t) : ℤ))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_shift_combinations_same_form t terms

theorem certifiedKill_diagonal_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_table

theorem exists_diagonalKill_le_82_paper (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_le_82_paper t ht

theorem exists_diagonalKill_on_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_on_table

theorem irrational_of_logarithmicDepth_diagonal_supply
    (hsupply : ∃ C : ℕ, ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      L ≤ Nat.log2 (4 * periodLcm t) + C ∧
        certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_logarithmicDepth_diagonal_supply hsupply

theorem periodLcm_seventeen_window_data :
    periodLcm 17 = 12252240 ∧ periodLcm 17 + 1 = 12252241 ∧
      2 * periodLcm 17 + 1 = 24504481 ∧ 2 * periodLcm 17 + 26 = 24504506 ∧
      diagonalPincerKillDepth 17 = 26 := @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_seventeen_window_data

end PalomarCorpus.E249.PaperStatementsI
