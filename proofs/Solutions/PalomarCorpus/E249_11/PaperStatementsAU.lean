/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerDecomposition
import Erdos249257.FirstHarmonicGap
import Erdos249257.FirstHarmonicPivot
import Erdos249257.LcmConeFlatness
import Erdos249257.LcmConeNonflat
import Erdos249257.PivotAntiReconstruction
import Erdos249257.PrimeJumpWindow
import Erdos249257.TotientActualLcmOrbitArithmetic
import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmDiagonalConditions
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmSeparationAndSign
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic
import ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase
import ErdosProblems.Erdos249.PaperCompleteR21.DyadicPrefixTailBound
import ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse
import ErdosProblems.Erdos249.PaperCompleteR21.FirstHarmonicBlockCriteria
import ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail
import ErdosProblems.Erdos249.PaperCompleteR21.LcmJumpPositionsAndCentralSlack
import ErdosProblems.Erdos249.PaperCompleteR21.PenultimateStaircaseAndRankCurvature
import ErdosProblems.Erdos249.PaperCompleteR21.PeriodMultipleAndSecondDifference
import ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels
import ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts
import ErdosProblems.Erdos249.PaperCompleteR21.ThreeParticularEquivalences
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseCertificateFailure
import ErdosProblems.Erdos249.PeriodMultipleEscape
import ErdosProblems.Skip.LadderT67
import Solutions.PalomarCorpus.E249_11.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAU
export PalomarCorpus.E249_11.Shared (ActualLcmTopEdgeResidueGap certifiedKill periodLcm totientTail windowDiscrepancy)

noncomputable def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m

noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

noncomputable def totientOverlapFactor (j x : ℕ) : ℕ :=
  (Nat.totient j / Nat.totient (Nat.gcd j x)) * Nat.gcd j x

noncomputable def lcmDivisorRayLetter (H j : ℕ) : ℤ :=
  let a := H / j
  ((totientOverlapFactor j (2 * a + 1) *
      Nat.totient (2 * a + 1) : ℕ) : ℤ) -
    ((totientOverlapFactor j (a + 1) *
      Nat.totient (a + 1) : ℕ) : ℤ)

noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

noncomputable def lcmRayArithmeticLetter (t j : ℕ) : ℤ :=
  if j ∣ periodLcm t then
    lcmDivisorRayLetter (periodLcm t) j
  else
    deltaTotient (periodLcm t) (periodLcm t + j)

noncomputable def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)

noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

noncomputable def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)

noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)

noncomputable def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)

noncomputable def primeJumpSharpKill (H p L : ℕ) : Prop :=
  primeJumpSharpRadius H p L <
      primeJumpWindowCommutator H p L % 2 ^ L ∧
    primeJumpWindowCommutator H p L % 2 ^ L <
      2 ^ L - primeJumpSharpRadius H p L

noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H

noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2

noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h

noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

noncomputable def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L

noncomputable def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)

noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))

noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L

theorem irrational_of_modFour_pulse_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] ∧
      ∃ K : ℕ, ∀ z : ℤ, |z| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) → z ≡ (2 : ℤ) [ZMOD 4] →
        ∃ i : ℕ, i ≤ K ∧
          ((p + i + 4 * h + 2 : ℕ) : ℤ) ≤ |carryOrbit (4 * h) p z i|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply hsupply

theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply hsupply

theorem irrational_of_primeJumpSharp_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ,
      0 < p ∧ primeJumpSharpKill (periodLcm t) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_primeJumpSharp_supply hsupply

theorem irrational_of_restrictedDepth_diagonal_supply (depthBound : ℕ → ℕ → Prop)
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      depthBound t L ∧ certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_restrictedDepth_diagonal_supply depthBound hsupply

theorem irrational_of_short_window_diagonal_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_short_window_diagonal_supply hsupply

theorem irrational_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_topEdgeResidueGapSupply hsupply

theorem irrational_of_upper_endpoint_gap_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_upper_endpoint_gap_supply hsupply

theorem lcmRayArithmeticLetter_eq_totient_difference (t j : ℕ) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.lcmRayArithmeticLetter_eq_totient_difference t j

theorem lcmRay_divisor_clean_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j) :
    Nat.gcd j (periodLcm t / j + 1) = 1
      ∧ Nat.gcd j (2 * (periodLcm t / j) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm t + j) : ℤ)
            - (Nat.totient (periodLcm t + j) : ℤ)
          = (Nat.totient j : ℤ)
              * ((Nat.totient (2 * (periodLcm t / j) + 1) : ℤ)
                  - (Nat.totient (periodLcm t / j + 1) : ℤ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_clean_formula t j hjdvd hclean

theorem lcmRay_divisor_denominators_pos {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    0 < j
      ∧ 0 < Nat.totient (Nat.gcd j (periodLcm t / j + 1))
      ∧ 0 < Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_denominators_pos t j hjdvd

theorem lcmRay_divisor_gcd_example :
    periodLcm 2 = 2
      ∧ Nat.gcd 2 (periodLcm 2 / 2 + 1) = 2
      ∧ Nat.gcd 2 (2 * (periodLcm 2 / 2) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm 2 + 2) : ℤ)
            - (Nat.totient (periodLcm 2 + 2) : ℤ) = 0
      ∧ (Nat.totient 2 : ℤ)
            * ((Nat.totient (2 * (periodLcm 2 / 2) + 1) : ℤ)
                - (Nat.totient (periodLcm 2 / 2 + 1) : ℤ)) = 1 := @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_gcd_example

theorem lcmRay_divisor_product_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    ((Nat.totient (2 * periodLcm t + j) : ℚ)
        - (Nat.totient (periodLcm t + j) : ℚ))
      = (Nat.totient j : ℚ) *
          ((Nat.gcd j (2 * (periodLcm t / j) + 1) : ℚ)
                * (Nat.totient (2 * (periodLcm t / j) + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1)) : ℚ)
            - (Nat.gcd j (periodLcm t / j + 1) : ℚ)
                * (Nat.totient (periodLcm t / j + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (periodLcm t / j + 1)) : ℚ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_product_formula t j hjdvd

theorem lcmRay_nondivisor_literal {t j : ℕ} (hjdvd : ¬ j ∣ periodLcm t) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) ∧
      lcmRayArithmeticLetter t j = deltaTotient (periodLcm t) (periodLcm t + j) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_nondivisor_literal t j hjdvd

theorem orbit_tail_diff_eq (h N : ℕ) :
    totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_eq h N

theorem orbit_tail_diff_firstChar_eq (h N : ℕ) :
    Complex.exp
        (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
        (((2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) * Complex.I) := @ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_firstChar_eq h N

theorem orbit_tail_diff_fract_eq_doubling_orbit (h N : ℕ) :
    Int.fract (totientTail (N + h) - totientTail N)
      = Int.fract
          ((fun x : ℝ => 2 * x)^[N]
            (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) := @ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_fract_eq_doubling_orbit h N

theorem orbit_tail_diff_sub_scaled_is_int (h N : ℕ) :
    ∃ z : ℤ,
      totientTail (N + h) - totientTail N
          - (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        = (z : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_sub_scaled_is_int h N

theorem orbit_tail_recurrence (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_recurrence N

theorem penultimate_shortWindow_difference_eq_half {a J K m : ℕ} (ha : 8 ≤ a)
    (hmPos : 0 < m) (hmK : m ≤ K)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlast : (Nat.totient (2 * periodLcm (2 ^ a) + (J + K)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K)) : ℤ)
        ≤ (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
    (hprefix : ∀ r : ℕ, r + 1 < m →
        (2 : ℤ) ^ (r + 1) ∣
          ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ)
            - (Nat.totient (periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ))) :
    ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - 1)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K - 1)) : ℤ))
        = (2 : ℤ) ^ (m - 1)
      ∧ (2 : ℤ) ^ m < 2 * ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ (4 : ℤ) ≤ ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ 3 ≤ m := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.penultimate_shortWindow_difference_eq_half a J K m ha hmPos hmK hshort hroom hlast hprefix

theorem periodLcm_four_eq_twelve : periodLcm 4 = 12 := @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_four_eq_twelve

theorem periodLcm_strict_jump_at_powerTwo_pred {a : ℕ} (ha : 1 ≤ a) :
    periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_powerTwo_pred a ha

theorem periodLcm_strict_jump_at_prime_pred {t₀ p : ℕ} (hp : p.Prime)
    (hpt : t₀ < p) :
    t₀ ≤ p - 1 ∧ periodLcm (p - 1) < periodLcm (p - 1 + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_prime_pred t₀ p hp hpt

theorem periodLcm_zero_and_one_eq_one :
    periodLcm 0 = 1 ∧ periodLcm 1 = 1 ∧ ¬ periodLcm 0 < periodLcm (0 + 1) := @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_zero_and_one_eq_one

theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L := @ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one h₀ N L hcert

theorem period_multiple_certificate_supply_iff :
    (∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
        ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_supply_iff

theorem pointwise_completeness_supplies_some_depth (h N : ℕ)
    (hnon : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L : ℕ, certifiedKill h N L := @ErdosProblems.Erdos249.PaperCompleteR21.pointwise_completeness_supplies_some_depth h N hnon

theorem primeJumpTailCommutator_notMem_int_of_central_window (H p L : ℕ)
    (hleft : (primeJumpSharpRadius H p L) < primeJumpWindowCommutator H p L % 2 ^ L)
    (hright : primeJumpWindowCommutator H p L % 2 ^ L
      < 2 ^ L - primeJumpSharpRadius H p L) :
    primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_notMem_int_of_central_window H p L hleft hright

theorem primeJumpTailCommutator_twelve_five_notMem_int :
    primeJumpTailCommutator 12 5 ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_twelve_five_notMem_int

theorem primeJump_witness_twelve_five_values :
    primeJumpWindowCommutator 12 5 15 = 149906 ∧
      primeJumpWindowCommutator 12 5 15 % 32768 = 18834 ∧
      primeJumpSharpRadius 12 5 15 = 282 ∧
      (282 : ℤ) < 18834 ∧ (18834 : ℤ) < 32486 := @ErdosProblems.Erdos249.PaperCompleteR21.primeJump_witness_twelve_five_values

theorem pulse_delta_of_divisor_data {H K p : ℕ} (hK : 2 ≤ K) (hp : p.Prime)
    (hmod : p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K])
    (htop : 2 ^ K ∣ Nat.totient (p + H))
    (hlower : ∀ j : ℕ, 1 ≤ j → j < K →
      2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) :
    deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K] := @ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data H K p hK hp hmod htop hlower

theorem rational_forces_four_tail_diagonals_integral
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ p : ℕ, 0 < p →
      (totientTail (2 * periodLcm t) - totientTail (periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
        (totientTail (2 * (p * periodLcm t)) - totientTail (p * periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral hrat

theorem rational_forces_period_multiple_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ m N : ℕ, N₀ ≤ N →
      totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality hrat

theorem rational_forces_pulse_class_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ B : ℕ, ∀ p : ℕ, B < p →
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] →
      ∃ z : ℤ, (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4] := @ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_pulse_class_integrality hrat

theorem rational_tail_period_explicit_witnesses
    (p : ℚ) (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ))
    (c v : ℕ) (hden : p.den = 2 ^ c * v) (hvodd : Odd v) :
    v ∣ 2 ^ Nat.totient v - 1 ∧
      (∀ N : ℕ, c ≤ N →
        ((2 : ℝ) ^ N * ((2 : ℝ) ^ Nat.totient v - 1)) *
            (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ N : ℕ, c ≤ N →
        totientTail (N + Nat.totient v) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses p hS c v hden hvodd

theorem real_part_bound_of_norm_bound {h X L : ℕ} (hX : (0 : ℝ) ≤ X)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (21 / 25 : ℝ) < 9 / 10 ∧
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := @ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound h X L hX hgap

theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9 := @ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight

theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound h N L hlow hhigh

theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2) := @ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound h N L

theorem shortWindowSupply_through_six_paper (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_through_six_paper a₀ ha₀

theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six

theorem shortWindow_totient_difference_pos {a j : ℕ} (ha : 8 ≤ a)
    (hjpos : 0 < j) (hjlt : j < 2 * 2 ^ a) :
    0 < (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + j) : ℤ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_totient_difference_pos a j ha hjpos hjlt

theorem short_window_diagonal_through_six (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six a₀ ha₀

theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6 := @ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses

theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational hirr h N hh

theorem tendsto_actualLcmRawErrorRadius_atTop_nhds_zero (a : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1))
      Filter.atTop (nhds 0) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.tendsto_actualLcmRawErrorRadius_atTop_nhds_zero a

theorem three_particular_equivalences :
    (PeriodMultipleKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (DTWWindowSeparatedPairs ↔
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (∀ H p q : ℕ, 0 < p → 0 < q →
          ((IsIntegralValue (totientTail (2 * H) - totientTail H)
              ∧ IsIntegralValue (totientTail (2 * (p * H)) - totientTail (p * H))
              ∧ IsIntegralValue (totientTail (2 * (q * H)) - totientTail (q * H))
              ∧ IsIntegralValue
                  (totientTail (2 * (p * q * H)) - totientTail (p * q * H)))
            ↔ IsIntegralValue (totientTail (2 * H) - totientTail H))) := @ErdosProblems.Erdos249.PaperCompleteR21.three_particular_equivalences

theorem topEdgeResidueGap_forces_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_forces_nonintegral a J K m ha hshort hgap

theorem topEdgeResidueGap_orbit_nonintegral {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_orbit_nonintegral a K m ha hshort hgap

theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded a J K m

theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds n

theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two N

theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K := @ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_construction_never_certifies H K hK hHK

theorem two_mul_totient_dvd_totient_second_difference {a j : ℕ} (ha : 4 ≤ a)
    (hj : 0 < j) (hsq : j * j ≤ 2 ^ a) :
    (2 * (Nat.totient j : ℤ)) ∣
          ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
      ∧ ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
          = (Nat.totient j : ℤ)
              * ((Nat.totient (3 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  - 2 * (Nat.totient (2 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  + (Nat.totient (periodLcm (2 ^ a) / j + 1) : ℤ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.two_mul_totient_dvd_totient_second_difference a j ha hj hsq

theorem upper_endpoint_condition_iff (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_condition_iff a J K m

theorem upper_endpoint_gap_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_gap_nonintegral a J K m ha hshort hgap

theorem weighted_shortWindow_band_iff_certifiedKill (t L : ℕ) :
    ((2 * (periodLcm t : ℤ) + L + 2 <
          (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L)
        ∧ (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L
            < 2 ^ L - (2 * (periodLcm t : ℤ) + L + 2))
      ↔ certifiedKill (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_band_iff_certifiedKill t L

theorem weighted_shortWindow_sum_eq_windowDiscrepancy (t L : ℕ) :
    (∑ r ∈ Finset.range L,
        ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
            - (Nat.totient (periodLcm t + (r + 1)) : ℤ)) * 2 ^ (L - 1 - r))
      = windowDiscrepancy (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_sum_eq_windowDiscrepancy t L

theorem windowDiscrepancy_diagonal_eq (M L : ℕ) :
    windowDiscrepancy M M L =
      (windowNumerator (2 * M) L : ℤ) - (windowNumerator M L : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.windowDiscrepancy_diagonal_eq M L

theorem windowFirstCos_unfolded (h N L : ℕ) :
    windowFirstCos h N L
      = Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))) := @ErdosProblems.Erdos249.PaperCompleteR21.windowFirstCos_unfolded h N L

theorem certifiedKill_101_300 : certifiedKill 101 300 11 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_101_300

theorem certifiedKill_121_300 : certifiedKill 121 300 10 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_121_300

theorem certifiedKill_125_300 : certifiedKill 125 300 18 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_125_300

theorem certifiedKill_127_300 : certifiedKill 127 300 11 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_127_300

theorem certifiedKill_128_300 : certifiedKill 128 300 11 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_128_300

theorem certifiedKill_67_300 : certifiedKill 67 300 11 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_67_300

theorem certifiedKill_81_300 : certifiedKill 81 300 13 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_81_300

theorem certifiedKill_97_300 : certifiedKill 97 300 13 := @ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_97_300

theorem periodMultipleKillSupply_iff_irrational :
    PeriodMultipleKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PeriodMultipleEscape.periodMultipleKillSupply_iff_irrational

theorem exists_diagonalKill_le_82 (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82 t ht

end PalomarCorpus.E249.PaperStatementsAU
