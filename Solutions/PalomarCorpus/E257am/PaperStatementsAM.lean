/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.CertificateKernel
import Erdos249257.CofinalStripReturn
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCutLocator
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderFixedTailSocket
import Erdos249257.HalfGapMass
import Erdos249257.TerminalOnlyCofinal
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import ErdosProblems.Erdos257.PaperCompleteR20.AchievementGeometry
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap
import ErdosProblems.Erdos257.PaperCompleteR20.MersenneConstantDecimal
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR21.AchievementSetTopologyAndFiniteHalf
import ErdosProblems.Erdos257.PaperCompleteR21.CentredCompletionAndDecisionBoundary
import ErdosProblems.Erdos257.PaperCompleteR21.EventualNonnegativeMargin
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyGapCriteria
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies
import ErdosProblems.Erdos257.PaperCompleteR21.OneSidedCertificateHierarchy
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit
import ErdosProblems.Erdos257.PaperCompleteR21.SharedPrefixFamiliesAndMeasureDichotomy
import ErdosProblems.Erdos257.PaperCompleteR21.SkipSafetyAndDivisorZeroRuns
import ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences
import Solutions.PalomarCorpus.E257am.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAM

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

noncomputable def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)

noncomputable def HalfCarryCofinalTerminalOnlyStrip : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ HalfTerminalOnlyStripWitness M

theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn hreturn

theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound hnonneg hbound

theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound hbound

theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := @Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg N

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem

theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := @Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess n

theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := @Erdos249257.half_mem_iff_every_actual_skip_survives

theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap := @Erdos249257.half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap

theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips hskips

theorem half_mem_mersenneAchievementSet_or_exists_fatal_gap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
          < 1 / 2 ∧
        (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
          + mersenneWeight (d + 1) := @Erdos249257.half_mem_mersenneAchievementSet_or_exists_fatal_gap

theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ) := @Erdos249257.half_ne_coe_finset_add_mersenneTail u d

theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n := @Erdos249257.mersenneGap_le n hn

theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := @Erdos249257.mersenneGap_tail_le N

theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) := @Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half u h0

theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1)) := @Erdos249257.summable_mersenneGap_shift N

theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1)) := @Erdos249257.summable_mersenneGap_succ

theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0) := @Erdos249257.tendsto_mersenneGap_tail_zero

theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := @ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry C D h

theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16 := @ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal

theorem mersenne_topology_quantitative : := @ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative

theorem paper_achievement_geometry :
    IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet = 1 ∧
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant ∧
    Function.Injective positiveMersenneDigitValue ∧
    ∀ x ∈ mersenneAchievementSet, ∃! A : Set ℕ,
      0 ∉ A ∧ positiveMersenneSupportValue A = x := @ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry

theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := @ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival

theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2 := @ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail

theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) : := @ErdosProblems.Erdos257.PaperCompleteR21.abs_supportValue_sub_le_mersenneTail A B K h

theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := @ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction t v ht hv

theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := @ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap h

theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N) := @ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound_cast d N hdN

theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n := @ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue_cast L N hLN

theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v := @ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint t u v d hu hv hut hvt

theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := @ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate

theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap := @ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate L N h

theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) := @ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing x hx

theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A) := @ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds A u d hu hagree

theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t := @ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation t u d hu hlo hhi

theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d := @ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval t u d hlo hhi

theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n) := @ErdosProblems.Erdos257.PaperCompleteR21.irrational_mersenneTail

theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K) := @ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add m K

theorem paper_achievement_set_topology :
    Continuous positiveMersenneDigitValue ∧
      Set.range positiveMersenneDigitValue = mersenneAchievementSet ∧
      IsCompact mersenneAchievementSet ∧
      IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧
      IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧
      volume mersenneAchievementSet = 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_achievement_set_topology

theorem paper_cpgs_equiv :
    ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
        0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips) ∧
      (∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv

theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := @ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test k J heta htest

theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry k

theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue k

theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := @ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence k hk

theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold k u L a hk hu ha hdecomp

theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff k

theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone k

theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto k

theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value k J

theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap k hk

theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := @ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc k

theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k := @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties k hk

theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip n

theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take n

theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability t v dep ht hv hvpos hdep K

theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary

theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap

theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k := @ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail k u L a hk hu ha hdecomp hsharp

theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧ := @ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv

theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy J

theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n := @ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast N n hn hnN

theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet := @ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem t

theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0) := @ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs

theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne m

theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J) := @ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet J hJ

theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) := @ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J

theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0) := @ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J

theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0 := @ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite J hJ

end PalomarCorpus.E257.PaperStatementsAM
