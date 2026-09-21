/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerDecomposition
import Erdos249257.FirstHarmonicGap
import Erdos249257.FirstHarmonicPivot
import Erdos249257.LcmConeFlatness
import Erdos249257.LcmConeNonflat
import Erdos249257.PivotAntiReconstruction
import Erdos249257.PrimeJumpWindow
import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmDiagonalConditions
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic
import ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase
import ErdosProblems.Erdos249.PaperCompleteR21.DyadicPrefixTailBound
import ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse
import ErdosProblems.Erdos249.PaperCompleteR21.FirstHarmonicBlockCriteria
import ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail
import ErdosProblems.Erdos249.PaperCompleteR21.LcmJumpPositionsAndCentralSlack
import ErdosProblems.Erdos249.PaperCompleteR21.PeriodMultipleAndSecondDifference
import ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels
import ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses
import ErdosProblems.Erdos249.PaperCompleteR21.ThreeParticularEquivalences
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseCertificateFailure
import ErdosProblems.Erdos249.PeriodMultipleEscape

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.DiagonalPincerDecomposition`,
`Erdos249257.FirstHarmonicGap`, `Erdos249257.FirstHarmonicPivot`,
`Erdos249257.LcmConeFlatness`, `Erdos249257.LcmConeNonflat`,
`Erdos249257.PivotAntiReconstruction`, `Erdos249257.PrimeJumpWindow`,
`Erdos249257.TotientActualLcmOrbitSeparation`,
`Erdos249257.TotientActualLcmTopEdgeStaircase`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmDiagonalConditions`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic`,
`ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase`,
`ErdosProblems.Erdos249.PaperCompleteR21.DyadicPrefixTailBound`,
`ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse`,
`ErdosProblems.Erdos249.PaperCompleteR21.FirstHarmonicBlockCriteria`,
`ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail`,
`ErdosProblems.Erdos249.PaperCompleteR21.LcmJumpPositionsAndCentralSlack`,
`ErdosProblems.Erdos249.PaperCompleteR21.PeriodMultipleAndSecondDifference`,
`ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels`,
`ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses`,
`ErdosProblems.Erdos249.PaperCompleteR21.ThreeParticularEquivalences`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseCertificateFailure`,
`ErdosProblems.Erdos249.PeriodMultipleEscape`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsAU

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

noncomputable def ActualLcmTopEdgeResidueGap (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
      windowDiscrepancy (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)

noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

noncomputable def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)

noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

noncomputable def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)

noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H

noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)

noncomputable def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)

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

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L

noncomputable def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)

noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

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

theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply hsupply

theorem lcmRay_divisor_gcd_example :
    periodLcm 2 = 2
      ∧ Nat.gcd 2 (periodLcm 2 / 2 + 1) = 2
      ∧ Nat.gcd 2 (2 * (periodLcm 2 / 2) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm 2 + 2) : ℤ)
            - (Nat.totient (periodLcm 2 + 2) : ℤ) = 0
      ∧ (Nat.totient 2 : ℤ)
            * ((Nat.totient (2 * (periodLcm 2 / 2) + 1) : ℤ)
                - (Nat.totient (periodLcm 2 / 2 + 1) : ℤ)) = 1 := @ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_gcd_example

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

theorem periodLcm_four_eq_twelve : periodLcm 4 = 12 := @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_four_eq_twelve

theorem periodLcm_zero_and_one_eq_one :
    periodLcm 0 = 1 ∧ periodLcm 1 = 1 ∧ ¬ periodLcm 0 < periodLcm (0 + 1) := @ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_zero_and_one_eq_one

theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one <;> assumption

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

theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six

theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6 := @ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses

theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational hirr h N hh

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

theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) := by
  simpa only [ActualLcmTopEdgeResidueGap, DTWWindowSeparatedPairs, DTWWindowSeparatedPairsAt, IsIntegralValue, PeriodMultipleKillSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, actualLcmHeight, actualLcmTailOrbit, carryOrbit, certifiedKill, certifiedRank2Kill, deltaTotient, diagonalTailDifferenceAt, lcmDivisorRayLetter, lcmRayArithmeticLetter, periodLcm, primeJumpSharpKill, primeJumpSharpRadius, primeJumpTailCommutator, primeJumpWindowCommutator, totientOverlapFactor, totientPrefix, totientTail, windowDiscrepancy, windowDiscrepancy2, windowFirstAngle, windowFirstCos, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded

theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds n

theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two N

theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K := @ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_construction_never_certifies H K hK hHK

theorem upper_endpoint_condition_iff (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) := by
  simpa only [ActualLcmTopEdgeResidueGap, DTWWindowSeparatedPairs, DTWWindowSeparatedPairsAt, IsIntegralValue, PeriodMultipleKillSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, actualLcmHeight, actualLcmTailOrbit, carryOrbit, certifiedKill, certifiedRank2Kill, deltaTotient, diagonalTailDifferenceAt, lcmDivisorRayLetter, lcmRayArithmeticLetter, periodLcm, primeJumpSharpKill, primeJumpSharpRadius, primeJumpTailCommutator, primeJumpWindowCommutator, totientOverlapFactor, totientPrefix, totientTail, windowDiscrepancy, windowDiscrepancy2, windowFirstAngle, windowFirstCos, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_condition_iff

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

end Erdos249257.ExternalVerification249PaperStatementsAU
