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
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.DiagonalPincerCertificatesT64`,
`Erdos249257.FirstHarmonicGap`, `Erdos249257.FirstHarmonicPivot`,
`Erdos249257.LcmConeNonflat`, `Erdos249257.PrimeJumpWindow`,
`Erdos249257.TotientActualLcmOrbitArithmetic`,
`Erdos249257.TotientActualLcmOrbitSeparation`, `Erdos249257.TotientTailCarryPeriod`,
`Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR20.FiniteCarryCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR20.LcmGridCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR20.TailDepthCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmDiagonalConditions`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmSeparationAndSign`,
`ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase`,
`ErdosProblems.Erdos249.PaperCompleteR21.DyadicPrefixTailBound`,
`ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse`,
`ErdosProblems.Erdos249.PaperCompleteR21.FirstHarmonicBlockCriteria`,
`ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail`,
`ErdosProblems.Erdos249.PaperCompleteR21.LcmJumpPositionsAndCentralSlack`,
`ErdosProblems.Erdos249.PaperCompleteR21.PenultimateStaircaseAndRankCurvature`,
`ErdosProblems.Erdos249.PaperCompleteR21.PeriodMultipleAndSecondDifference`,
`ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses`,
`ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts`,
`ErdosProblems.Erdos249.PaperCompleteR21.SimultaneousShiftCertificateDepth`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicHalfPulseAndAccumulatedResidue`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsAT

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def directedCertifiedKill (h N L : ℕ) : Prop :=
  (N + L + 2 : ℤ) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
    windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
      (2 : ℤ) ^ L - (N + h + L + 2 : ℤ)

noncomputable def CofinalDirectedLcmCertificateSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
    directedCertifiedKill (periodLcm t) (periodLcm t) L

noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

noncomputable def actualLcmRawErrorRadius (a q : ℕ) : ℝ :=
  ((2 * actualLcmHeight a + 2 * q + 3 : ℕ) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

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

noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

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

noncomputable def DTWFirstHarmonicNormGap : Prop :=
  ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
    max X₀ 1 ≤ X ∧
    16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
    ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖
      ≤ (21 / 25 : ℝ) * X

noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]

noncomputable def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0

noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))

noncomputable def prescribedOddIndex (a : ℕ) : ℕ := (Nat.log2 (periodLcm (2 ^ a)) + 10) / 2

/-- States prop:deposits from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_all_imported_through_t64 in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certifiedKill_diagonal_all_imported_through_t64 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t) := by
  sorry

/-- States prop:iffs from the long record for Erdős problem #249. Transported from
Erdos249257.irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      CofinalDirectedLcmCertificateSupply := by
  sorry

/-- States catalogue:cert:b6, prop:B6-inv from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  sorry

/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L := by
  sorry

/-- States catalogue:cert:b5 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1) := by
  sorry

/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ) := by
  sorry

/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L := by
  sorry

/-- States catalogue:cert:b6, prop:B6-inv from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:b6 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_fractional_parts
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      Int.fract (totientTail ((q + m) * periodLcm t)) =
        Int.fract (totientTail (q * periodLcm t)) := by
  sorry

/-- States catalogue:cert:b7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_multiplier_positive in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_multiplier_positive (t q m L : ℕ)
    (hc : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 0 < m := by
  sorry

/-- States catalogue:cert:b6, catalogue:cert:b7, prop:B6-inv from the long record for Erdős
problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L := by
  sorry

/-- States catalogue:cert:a2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem short_lcm_window_nondivisor (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ periodLcm t) :
    ∃ p a : ℕ, Nat.Prime p ∧ 1 ≤ a ∧ j = p ^ a ∧ t < j := by
  sorry

/-- States catalogue:cert:a6 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2 := by
  sorry

/-- States catalogue:cert:b5 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2)) := by
  sorry

/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawErrorRadius_tendsto_zero in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcmRawErrorRadius_tendsto_zero (a : ℕ) :
    Filter.Tendsto (fun q : ℕ => actualLcmRawErrorRadius a q) Filter.atTop (nhds 0) := by
  sorry

/-- States prop:SK-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  sorry

/-- States prop:SEP-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_global_to_local in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcmTailOrbit_global_to_local (a : ℕ) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      = (2 : ℝ) ^ periodLcm (2 ^ a) * ((2 : ℝ) ^ periodLcm (2 ^ a) - 1)
            * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - ((totientPrefix (2 * periodLcm (2 ^ a)) : ℝ)
              - (totientPrefix (periodLcm (2 ^ a)) : ℝ)) := by
  sorry

/-- States prop:SGN-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_pos in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmTailOrbit_pos {a : ℕ} (ha : 8 ≤ a) :
    0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_corridor_pos in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcm_corridor_pos {a : ℕ} (ha : 8 ≤ a) :
    (∀ J : ℕ, J + (a + 6) < 2 * 2 ^ a →
        0 < totientTail (2 * periodLcm (2 ^ a) + J)
              - totientTail (periodLcm (2 ^ a) + J)) ∧
      0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  sorry

/-- States prop:SGN-03 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_integral_forces_topEdgeResidue_paper in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcm_integral_forces_topEdgeResidue_paper {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    (hint : ∃ d : ℤ, (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J)
        - totientTail (periodLcm (2 ^ a) + J)) :
    ∃ e : ℤ,
      ((e : ℝ) = totientTail (2 * periodLcm (2 ^ a) + J + K)
          - totientTail (periodLcm (2 ^ a) + J + K))
        ∧ windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
              % (2 : ℤ) ^ K
            = (2 : ℤ) ^ K - e
        ∧ 0 < e
        ∧ e < ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
        ∧ ((2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
              < windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
                  % (2 : ℤ) ^ K
            ∧ windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
                  % (2 : ℤ) ^ K < (2 : ℤ) ^ K)
        ∧ (2 : ℤ) ^ K ∣
            windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K + e := by
  sorry

/-- States prop:SGN-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_tailDiff_shift_pos_paper in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcm_tailDiff_shift_pos_paper {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 < totientTail (2 * periodLcm (2 ^ a) + J)
          - totientTail (periodLcm (2 ^ a) + J) := by
  sorry

/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X := by
  sorry

/-- States thm:hgap-subset from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry

/-- States prop:route4 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_fullDepth_phase_separation in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certifiedKill_of_fullDepth_phase_separation (h N : ℕ)
    (hsep : ∀ k : ℤ,
      2 * ((N : ℝ) + 2 * h + 2) / 2 ^ h <
        |(2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (k : ℝ)|) :
    certifiedKill h N h := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_halfModulus_residue in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certifiedKill_of_halfModulus_residue {h N L : ℕ} (hL : 1 ≤ L)
    (hcong : windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L])
    (hsmall : ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    certifiedKill h N L := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_eight_shifts_basepoint_twelve in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem commonCertificate_eight_shifts_basepoint_twelve :
    ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_sixteen_shifts_basepoint_fourteen
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem commonCertificate_sixteen_shifts_basepoint_fourteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_height_lt_letter in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem corridor_height_lt_letter {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) < 8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_letter_pos in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem corridor_letter_pos {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j := by
  sorry

/-- States prop:AR-07 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.diagonal_certificate_unfolded in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem diagonal_certificate_unfolded (a L : ℕ) :
    certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L ↔
      (((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ) <
          windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L <
          2 ^ L - ((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ)) := by
  sorry

/-- States prop:CP-06 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7 := by
  sorry

/-- States prop:CP-06 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_prefix_tail_le (N : ℕ) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem eventual_integral_tailDiff_twoAdic_half_pulse {H K N₀ : ℕ} (hK : 2 ≤ K)
    (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry

/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry

/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry

/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States prop:TE-03-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_twoBitResidueTest in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certifiedKill_iff_twoBitResidueTest (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      ∃ s b : ℕ,
        certifiedKill h (N + s) (b + 1) ∨
          (N + s + h + b + 4 < 2 ^ b
            ∧ (2 : ℤ) ^ b ≤ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
            ∧ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
                < 3 * (2 : ℤ) ^ b) := by
  sorry

/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry

/-- States thm:hgap-real from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry

/-- States thm:hgap-subset from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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
    ∃ N ∈ T, certifiedKill h N L := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_growingShift_simultaneous_certificate_iff_irrational
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem exists_growingShift_simultaneous_certificate_iff_irrational :
    (∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
        ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, ∀ h ∈ Finset.Icc 1 (f N),
          certifiedKill h N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_periodLcm_strict_jump_ge_paper in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_periodLcm_strict_jump_ge_paper (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1) := by
  sorry

/-- States prop:TA-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_prime_integral_tailDiff_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_half_pulse_window in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_prime_twoAdic_half_pulse_window (H K B : ℕ) (hK : 2 ≤ K)
    (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry

/-- States prop:TA-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_prime_twoAdic_pulse_block (K H B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_simultaneous_depth_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N M : ℕ)
    (hM : 1 ≤ M) :
    ∃ L, ∀ h ∈ Finset.Icc 1 M, certifiedKill h N L := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_simultaneous_depth_succ_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N : ℕ) :
    ∃ L, ∀ h ∈ Finset.Icc 1 (N + 1), certifiedKill h N L := by
  sorry

/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := by
  sorry

/-- States prop:FR-02-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.fixedRank_cleanWindow_structure in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fixedRank_cleanWindow_structure {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    j ∣ periodLcm (2 ^ a)
      ∧ (∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm (2 ^ a) / j)
      ∧ 2 * j ≤ 2 ^ a
      ∧ 2 * j ∣ periodLcm (2 ^ a)
      ∧ 2 ≤ periodLcm (2 ^ a) / j
      ∧ Even (periodLcm (2 ^ a) / j)
      ∧ (∀ q : ℕ, 0 < q → q ≤ 3 →
          Nat.gcd j (q * (periodLcm (2 ^ a) / j) + 1) = 1
            ∧ Odd (q * (periodLcm (2 ^ a) / j) + 1)
            ∧ 2 < q * (periodLcm (2 ^ a) / j) + 1
            ∧ Even (Nat.totient (q * (periodLcm (2 ^ a) / j) + 1))) := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282 := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ) := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L := by
  sorry

/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem integral_carry_strictly_between {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    0 < carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) ∧
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) := by
  sorry

/-- States prop:TE-04 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.integral_tail_forces_upper_endpoint_residue in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem integral_tail_forces_upper_endpoint_residue {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)) :
    (2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K ∧
      windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K <
        (2 : ℤ) ^ K := by
  sorry

/-- States prop:NI-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_iff_diagonal_orbit_nonintegrality in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_iff_diagonal_orbit_nonintegrality :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
          Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_accumulated_halfModulus_supply
    (hsupply : ∀ h : ℕ, 1 ≤ h → ∀ N₀ : ℕ, ∃ N L : ℕ, N₀ ≤ N ∧ 1 ≤ L ∧
      windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L] ∧
      ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:SEP-03 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_diagonal_orbit_separation_supply in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_diagonal_orbit_separation_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a : ℕ, max 2 a₀ ≤ a ∧ ∀ z : ℤ,
      (1 : ℝ) / 32 +
          ((2 * periodLcm (2 ^ a) + 2 * prescribedOddIndex a + 3 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * prescribedOddIndex a + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States catalogue:mob:e2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_four_tail_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ, 1 ≤ p ∧
      ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ) <
        (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L ∧
      (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L <
        2 ^ L - ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAT
