/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.CertificateKernel
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderFullShellSeamBridge
import Solutions.PalomarCorpus.E257_22.Statement

open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsF
export PalomarCorpus.E257_22.Shared (CofinalExactLocalMersenneHalfRows CofinalPositiveHalfGreedySkips ExactLocalMersenneHalfRow SkippedCoreCriticalQuotientSupply greedyMersenneRemainderRat localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)

noncomputable def futureSkipCapacity
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * futureSkipCapacity A n J +
        (by
          classical
          exact if n + J + 1 ∈ A then 0 else 1)

noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1

noncomputable def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k

noncomputable def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n

noncomputable def HalfGreedySkippedPrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

theorem cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    CofinalExactLocalMersenneHalfRows := by
  set_option smartUnfolding false in
  exact @Erdos249257.cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips hskips

theorem eq_halfGreedyPrefixSupport_of_critical_crossing
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) := by
  set_option smartUnfolding false in
  exact @Erdos249257.eq_halfGreedyPrefixSupport_of_critical_crossing D c hc hD hbelow hcross

theorem exactLocalMersenneHalfRow_of_positiveHalfGreedySkip
    {c : ℕ} (hc : 4 ≤ c)
    (hpos : 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  set_option smartUnfolding false in
  exact @Erdos249257.exactLocalMersenneHalfRow_of_positiveHalfGreedySkip c hc hpos hskip

theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply := by
  set_option smartUnfolding false in
  exact @Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix hpre

theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply := by
  set_option smartUnfolding false in
  exact @Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake

theorem halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
    {c : ℕ} (hc : 4 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
        (futureSkipCapacity
          (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ) := by
  set_option smartUnfolding false in
  exact @Erdos249257.halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage c hc hskip

theorem halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
    {c t : ℕ} (hc : 4 ≤ c) (htPos : 0 < t) (ht : t ≤ c - 3)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (htake : ∀ j ∈ Finset.range (t - 1),
      mersenneWeightRat (c + j + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c + j))
    (hfuture : greedyMersenneRemainderRat (1 / 2 : ℚ) (c + t - 1) <
      mersenneWeightRat (c + t))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  set_option smartUnfolding false in
  exact @Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock c t hc htPos ht hskip htake hfuture hroom

theorem halfGreedy_precriticalSuffix_lt_of_next_skip
    {c : ℕ} (hc : 6 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (hnext : greedyMersenneRemainderRat (1 / 2 : ℚ) c <
      mersenneWeightRat (c + 1)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  set_option smartUnfolding false in
  exact @Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip c hc hskip hnext

theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative hsign

theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply := by
  set_option smartUnfolding false in
  exact @Erdos249257.skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped

end PalomarCorpus.E257.PaperStatementsF
