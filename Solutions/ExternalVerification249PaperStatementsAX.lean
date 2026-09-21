/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalFreshLossBridge
import Erdos249257.FirstHarmonicPivot
import Erdos249257.JointExponentTransport
import Erdos249257.LcmConeNonflat
import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteGridCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.SpecifiedTailPeriod
import ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation
import ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection
import ErdosProblems.Erdos249.PaperCompleteR21.TemperedOrbitAndSquaredMersenneTail
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeChainPaperBand
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.DiagonalFreshLossBridge`,
`Erdos249257.FirstHarmonicPivot`, `Erdos249257.JointExponentTransport`,
`Erdos249257.LcmConeNonflat`, `Erdos249257.TotientActualLcmTopEdgeStaircase`,
`Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR20.FiniteGridCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR20.SpecifiedTailPeriod`,
`ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation`,
`ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection`,
`ErdosProblems.Erdos249.PaperCompleteR21.TemperedOrbitAndSquaredMersenneTail`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeChainPaperBand`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation`.
-/

open scoped BigOperators
open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsAX

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

noncomputable def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10

noncomputable def oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  let m := canonicalAdjacentSuffixDepth t
  if Even m then m + 1 else m

noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)

noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)

noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M

noncomputable def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)

noncomputable def PowerTwoActualFinalTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|

noncomputable def PowerTwoFlexibleActualTerminalDominanceSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q

noncomputable def PowerTwoFlexibleActualTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|

noncomputable def powerTwoInheritedIncrement (a r : ℕ) : ℤ :=
  if Even r then
    2 * diagonalWindowIncrement (2 ^ a - 1) r
  else
    diagonalWindowIncrement (2 ^ a - 1) r

noncomputable def powerTwoFreshOddIncrement (a q : ℕ) : ℤ :=
  diagonalWindowIncrement (2 ^ a) (2 * q + 1)

noncomputable def powerTwoOddDepthCorrection (a n : ℕ) : ℤ :=
  powerTwoFreshOddIncrement a (n + 1) -
    2 * powerTwoInheritedIncrement a (n + 1) +
    powerTwoInheritedIncrement a (n + 2)

noncomputable def powerTwoOddHalfCorrectionWord (a : ℕ) : ℕ → ℤ
  | 0 => 0
  | q + 1 =>
      4 * powerTwoOddHalfCorrectionWord a q +
        powerTwoOddDepthCorrection a q / 2

noncomputable def PowerTwoOddGuardTopEdgeHalfWordBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
    powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
      (4 : ℤ) ^ q -
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)

noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)

noncomputable def diagonalSuffixResidue (t J m : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
    (windowNumerator (periodLcm t + J) m : ℤ)) % 2 ^ m

noncomputable def diagonalAdjacentSuffixResidue (t J m : ℕ) : ℤ :=
  (diagonalSuffixResidue t (J + 1) m -
    diagonalSuffixResidue t J m) % 2 ^ m

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L

noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

noncomputable def paperGridNumerator (H L q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 L, Nat.totient (q * H + j) * 2 ^ (L - j)

noncomputable def paperGridCertificate (H L : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((paperGridNumerator H L qi : ℤ) - paperGridNumerator H L qj) % 2 ^ L

noncomputable def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)

theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair H L Q hQ hfloor hcert

theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := @ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq H L q

theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period a c v hv hodd hS

theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1)) := @ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq H L

theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window H L hH hlow hhigh

theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error H L hH

theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) := by
  simpa only [ActualLcmTopEdgeResidueGap, PaperAdjacentSuffixMidbandSupply, PowerTwoActualFinalTopEdgeMagnitudeSupply, PowerTwoActualLcmOrbitNonintegralitySupply, PowerTwoActualLcmOrbitSeparationSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, PowerTwoAdjacentSuffixMidbandSupply, PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, PowerTwoFlexibleActualTerminalDominanceSupply, PowerTwoFlexibleActualTopEdgeMagnitudeSupply, PowerTwoOddGuardTopEdgeHalfWordBandSupply, actualCenteredLift, actualLcmHeight, actualLcmRawApprox, actualLcmRawErrorRadius, actualLcmTailOrbit, actualOddHalfCenteredLift, canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth, carryOrbit, deltaTotient, diagonalAdjacentSuffixRawBlock, diagonalAdjacentSuffixResidue, diagonalSuffixResidue, diagonalWindowIncrement, joint35ConeWindow, lcmHeight, oddGuardedCanonicalAdjacentSuffixDepth, paperGridCertificate, paperGridNumerator, periodLcm, powerTwoFreshOddIncrement, powerTwoInheritedIncrement, powerTwoOddDepthCorrection, powerTwoOddHalfCorrectionWord, prescribedOddIndex, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded

theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re := @ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one h L T

theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ)) := @ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series H

theorem tailDifference_sub_rationalApproximation (H D : ℕ) :
    totientTail (2 * H) - totientTail H -
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
          (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
            (1 / 2 +
              ∑ d ∈ Finset.Icc 1 D,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                  (((2 : ℝ) ^ d - 1) ^ 2))) =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        ∑' k : ℕ,
          ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := @ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation H D

theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q := by
  simpa only [ActualLcmTopEdgeResidueGap, PaperAdjacentSuffixMidbandSupply, PowerTwoActualFinalTopEdgeMagnitudeSupply, PowerTwoActualLcmOrbitNonintegralitySupply, PowerTwoActualLcmOrbitSeparationSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, PowerTwoAdjacentSuffixMidbandSupply, PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, PowerTwoFlexibleActualTerminalDominanceSupply, PowerTwoFlexibleActualTopEdgeMagnitudeSupply, PowerTwoOddGuardTopEdgeHalfWordBandSupply, actualCenteredLift, actualLcmHeight, actualLcmRawApprox, actualLcmRawErrorRadius, actualLcmTailOrbit, actualOddHalfCenteredLift, canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth, carryOrbit, deltaTotient, diagonalAdjacentSuffixRawBlock, diagonalAdjacentSuffixResidue, diagonalSuffixResidue, diagonalWindowIncrement, joint35ConeWindow, lcmHeight, oddGuardedCanonicalAdjacentSuffixDepth, paperGridCertificate, paperGridNumerator, periodLcm, powerTwoFreshOddIncrement, powerTwoInheritedIncrement, powerTwoOddDepthCorrection, powerTwoOddHalfCorrectionWord, prescribedOddIndex, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded

theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  simpa only [ActualLcmTopEdgeResidueGap, PaperAdjacentSuffixMidbandSupply, PowerTwoActualFinalTopEdgeMagnitudeSupply, PowerTwoActualLcmOrbitNonintegralitySupply, PowerTwoActualLcmOrbitSeparationSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, PowerTwoAdjacentSuffixMidbandSupply, PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, PowerTwoFlexibleActualTerminalDominanceSupply, PowerTwoFlexibleActualTopEdgeMagnitudeSupply, PowerTwoOddGuardTopEdgeHalfWordBandSupply, actualCenteredLift, actualLcmHeight, actualLcmRawApprox, actualLcmRawErrorRadius, actualLcmTailOrbit, actualOddHalfCenteredLift, canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth, carryOrbit, deltaTotient, diagonalAdjacentSuffixRawBlock, diagonalAdjacentSuffixResidue, diagonalSuffixResidue, diagonalWindowIncrement, joint35ConeWindow, lcmHeight, oddGuardedCanonicalAdjacentSuffixDepth, paperGridCertificate, paperGridNumerator, periodLcm, powerTwoFreshOddIncrement, powerTwoInheritedIncrement, powerTwoOddDepthCorrection, powerTwoOddHalfCorrectionWord, prescribedOddIndex, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded

theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  simpa only [ActualLcmTopEdgeResidueGap, PaperAdjacentSuffixMidbandSupply, PowerTwoActualFinalTopEdgeMagnitudeSupply, PowerTwoActualLcmOrbitNonintegralitySupply, PowerTwoActualLcmOrbitSeparationSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, PowerTwoAdjacentSuffixMidbandSupply, PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, PowerTwoFlexibleActualTerminalDominanceSupply, PowerTwoFlexibleActualTopEdgeMagnitudeSupply, PowerTwoOddGuardTopEdgeHalfWordBandSupply, actualCenteredLift, actualLcmHeight, actualLcmRawApprox, actualLcmRawErrorRadius, actualLcmTailOrbit, actualOddHalfCenteredLift, canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth, carryOrbit, deltaTotient, diagonalAdjacentSuffixRawBlock, diagonalAdjacentSuffixResidue, diagonalSuffixResidue, diagonalWindowIncrement, joint35ConeWindow, lcmHeight, oddGuardedCanonicalAdjacentSuffixDepth, paperGridCertificate, paperGridNumerator, periodLcm, powerTwoFreshOddIncrement, powerTwoInheritedIncrement, powerTwoOddDepthCorrection, powerTwoOddHalfCorrectionWord, prescribedOddIndex, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded

theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) := by
  simpa only [ActualLcmTopEdgeResidueGap, PaperAdjacentSuffixMidbandSupply, PowerTwoActualFinalTopEdgeMagnitudeSupply, PowerTwoActualLcmOrbitNonintegralitySupply, PowerTwoActualLcmOrbitSeparationSupply, PowerTwoActualLcmTopEdgeResidueGapSupply, PowerTwoAdjacentSuffixMidbandSupply, PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, PowerTwoFlexibleActualTerminalDominanceSupply, PowerTwoFlexibleActualTopEdgeMagnitudeSupply, PowerTwoOddGuardTopEdgeHalfWordBandSupply, actualCenteredLift, actualLcmHeight, actualLcmRawApprox, actualLcmRawErrorRadius, actualLcmTailOrbit, actualOddHalfCenteredLift, canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth, carryOrbit, deltaTotient, diagonalAdjacentSuffixRawBlock, diagonalAdjacentSuffixResidue, diagonalSuffixResidue, diagonalWindowIncrement, joint35ConeWindow, lcmHeight, oddGuardedCanonicalAdjacentSuffixDepth, paperGridCertificate, paperGridNumerator, periodLcm, powerTwoFreshOddIncrement, powerTwoInheritedIncrement, powerTwoOddDepthCorrection, powerTwoOddHalfCorrectionWord, prescribedOddIndex, totientPrefix, totientTail, windowDiscrepancy, windowFirstAngle, windowFirstExp, windowNumerator] using ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded

theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure n hn

end Erdos249257.ExternalVerification249PaperStatementsAX
