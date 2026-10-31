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
import Erdos249257.HalfCylinderFixedTailSocket
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap
import Solutions.PalomarCorpus.E257_32.Statement

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsD
export PalomarCorpus.E257_32.Shared (affineBinaryOrbit erdosSupportSeries greedyMersenneRemainder halfStripBound integerHalfCarry mersenneWeight supportCoeff)

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n

noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

noncomputable def halfGreedyPrefixRat (n : ℕ) : ℚ :=
  finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2

noncomputable def halfGreedyPrefixDenominator (n : ℕ) : ℕ :=
  (halfGreedyPrefixRat n).den

noncomputable def halfGreedyResidualDisplayedNumerator (n : ℕ) : ℤ :=
  (halfGreedyPrefixDenominator n : ℤ) -
    2 * (halfGreedyPrefixRat n).num

noncomputable def halfGreedyNextDyadicExcessNumerator (n : ℕ) : ℤ :=
  nextDyadicExcessIntNumerator
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m

theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn hreturn

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
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound hnonneg hbound

theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound hbound

theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg N

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem

theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := by
  set_option smartUnfolding false in
  exact @Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess n

theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_iff_every_actual_skip_survives

theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips hskips

theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry C D h

theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival

end PalomarCorpus.E257.PaperStatementsD
