/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.FirstHarmonicGap
import Erdos249257.FirstHarmonicPivot
import Erdos249257.LcmConeNonflat
import Erdos249257.PrimeJumpWindow
import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.TotientTailCarryPeriod
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR20.LcmGridCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.TailDepthCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase
import ErdosProblems.Erdos249.PaperCompleteR21.DyadicPrefixTailBound
import ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse
import ErdosProblems.Erdos249.PaperCompleteR21.FirstHarmonicBlockCriteria
import ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail
import ErdosProblems.Erdos249.PaperCompleteR21.PenultimateStaircaseAndRankCurvature
import ErdosProblems.Erdos249.PaperCompleteR21.PeriodMultipleAndSecondDifference
import ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts
import ErdosProblems.Erdos249.PaperCompleteR21.SimultaneousShiftCertificateDepth
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicHalfPulseAndAccumulatedResidue
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion
import Solutions.PalomarCorpus.E249at.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAT

theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion r h N L hcert hden

theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L := @ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth h N L hc

theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L := @ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices h N L hc

theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N) := @ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part N

theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2 := @ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error h N L

theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2)) := @ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample

theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le h N L

theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  simpa only [CofinalDirectedLcmCertificateSupply, DTWFirstHarmonicNormGap, actualLcmHeight, actualLcmRawErrorRadius, actualLcmTailOrbit, carryOrbit, certifiedKill, deltaTotient, diagonalPincerCertificateScalesThroughT64, diagonalPincerKillDepthThroughT64, diagonalTailDifferenceAt, directedCertifiedKill, lcmDivisorRayLetter, lcmRayArithmeticLetter, periodLcm, prescribedOddIndex, primeJumpTailCommutator, primeJumpWindowCommutator, totientOverlapFactor, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstCos, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference

theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X := @ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded

theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form h X L hX hroom hgap

theorem certifiedKill_of_fullDepth_phase_separation (h N : ℕ)
    (hsep : ∀ k : ℤ,
      2 * ((N : ℝ) + 2 * h + 2) / 2 ^ h <
        |(2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (k : ℝ)|) :
    certifiedKill h N h := @ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_fullDepth_phase_separation h N hsep

theorem certifiedKill_of_halfModulus_residue {h N L : ℕ} (hL : 1 ≤ L)
    (hcong : windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L])
    (hsmall : ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_halfModulus_residue h N L hL hcong hsmall

theorem commonCertificate_eight_shifts_basepoint_twelve :
    ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16 := @ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_eight_shifts_basepoint_twelve

theorem commonCertificate_sixteen_shifts_basepoint_fourteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := @ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_sixteen_shifts_basepoint_fourteen

theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7 := @ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example

theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff h N

theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N := @ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd N

theorem dyadic_prefix_tail_le (N : ℕ) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N := @ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le N

theorem eventual_integral_tailDiff_twoAdic_half_pulse {H K N₀ : ℕ} (hK : 2 ≤ K)
    (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse <;> assumption

theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational hrat

theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound h X L hX hroom hgap

theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound h X L hX hroom hre

theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral h N

theorem exists_certifiedKill_iff_twoBitResidueTest (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      ∃ s b : ℕ,
        certifiedKill h (N + s) (b + 1) ∨
          (N + s + h + b + 4 < 2 ^ b
            ∧ (2 : ℤ) ^ b ≤ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
            ∧ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
                < 3 * (2 : ℤ) ^ b) := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_twoBitResidueTest h N

theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound h X L hX hroom hgap

theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound h X L hX hroom hgap

theorem exists_certifiedKill_of_subset_real_part_bound {h X L : ℕ}
    (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T,
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound h X L T hTlt hTne hroom hgap

theorem exists_growingShift_simultaneous_certificate_iff_irrational :
    (∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
        ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, ∀ h ∈ Finset.Icc 1 (f N),
          certifiedKill h N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.exists_growingShift_simultaneous_certificate_iff_irrational

theorem exists_prime_integral_tailDiff_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse <;> assumption

theorem exists_prime_twoAdic_half_pulse_window (H K B : ℕ) (hK : 2 ≤ K)
    (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := @ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_half_pulse_window H K B hK hHK

theorem exists_prime_twoAdic_pulse_block (K H B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := @ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block K H B hK hHK

theorem exists_simultaneous_depth_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N M : ℕ)
    (hM : 1 ≤ M) :
    ∃ L, ∀ h ∈ Finset.Icc 1 M, certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational hS N M hM

theorem exists_simultaneous_depth_succ_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N : ℕ) :
    ∃ L, ∀ h ∈ Finset.Icc 1 (N + 1), certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational hS N

theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := @ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound h X L hgap

theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282 := @ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance

theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H := @ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq H p

theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound H p L hlow hhigh

theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound H p L

theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L := @ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq H p L

theorem irrational_of_accumulated_halfModulus_supply
    (hsupply : ∀ h : ℕ, 1 ≤ h → ∀ N₀ : ℕ, ∃ N L : ℕ, N₀ ≤ N ∧ 1 ≤ L ∧
      windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L] ∧
      ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply hsupply

theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition hgap

theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply hsupply

theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap hgap

end PalomarCorpus.E249.PaperStatementsAT
