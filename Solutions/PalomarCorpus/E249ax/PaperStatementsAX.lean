/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalFreshLossBridge
import Erdos249257.FirstHarmonicPivot
import Erdos249257.JointExponentTransport
import Erdos249257.LcmConeNonflat
import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Erdos249257.TotientActualLcmOrbitNonintegrality
import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteGridCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.SpecifiedTailPeriod
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmDiagonalConditions
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmSeparationAndSign
import ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation
import ErdosProblems.Erdos249.PaperCompleteR21.LcmJumpPositionsAndCentralSlack
import ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection
import ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels
import ErdosProblems.Erdos249.PaperCompleteR21.TemperedOrbitAndSquaredMersenneTail
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeChainPaperBand
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions
import Solutions.PalomarCorpus.E249ax.Statement

open scoped BigOperators
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAX

theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair H L Q hQ hfloor hcert

theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational hs

theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := @ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq H L q

theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period a c v hv hodd hS

theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit (a q : ℕ) : := @ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit a q

theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) : := @ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form a q

theorem abs_orbit_sub_rawApprox_lt (a q : ℕ) : := @ErdosProblems.Erdos249.PaperCompleteR21.abs_orbit_sub_rawApprox_lt a q

theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat a q

theorem canonicalAdjacentSuffixCentralSlack_paper_formula (t : ℕ) :
    canonicalAdjacentSuffixCentralSlack t =
      min ((windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                (Nat.log2 (periodLcm t) + 10)
              - windowDiscrepancy (periodLcm t) (periodLcm t)
                (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)
          - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5))
        (2 ^ (Nat.log2 (periodLcm t) + 10)
            - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5)
          - (windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                 (Nat.log2 (periodLcm t) + 10)
               - windowDiscrepancy (periodLcm t) (periodLcm t)
                 (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)) := @ErdosProblems.Erdos249.PaperCompleteR21.canonicalAdjacentSuffixCentralSlack_paper_formula t

theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := @ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude

theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral a q ha hshort hfit hesc

theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) := @ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity a q ha hshort hfit z hz

theorem irrational_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_actualLcmOrbitSeparationSupply hsupply

theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply hsupply

theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply hsupply

theorem irrational_of_powerTwo_postJump_slack_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_powerTwo_postJump_slack_supply hsupply

theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply hsupply

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

theorem lcmHeight_eq_periodLcm (t : ℕ) : lcmHeight t = periodLcm t := @ErdosProblems.Erdos249.PaperCompleteR21.lcmHeight_eq_periodLcm t

theorem oddGuarded_depth_eq_prescribed (a : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * prescribedOddIndex a + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.oddGuarded_depth_eq_prescribed a

theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q := @ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec a q ha

theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply := @ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband hsupply

theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply := @ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude hsupply

theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply := @ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand hsupply

theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply := @ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality

theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) := @ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply

theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := @ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality

theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded

theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) := @ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations

theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := @ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband hsupply

theorem rawApprox_separation_of_orbit_separation {a q : ℕ}
    (hsep : ∀ z : ℤ,
      (1 : ℝ) / 32 + ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) ≤ := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.rawApprox_separation_of_orbit_separation <;> assumption

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
          2 * actualOddHalfCenteredLift a q := @ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded

theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := @ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded

theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := @ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded

theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded

theorem te_chain_relations :
    (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoAdjacentSuffixMidbandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        PowerTwoActualLcmOrbitNonintegralitySupply) := @ErdosProblems.Erdos249.PaperCompleteR21.te_chain_relations

theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral a q ha hshort hfit hdom

theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m := @ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband a m hroom hlo hhi

theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1 := @ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure n hn

end PalomarCorpus.E249.PaperStatementsAX
