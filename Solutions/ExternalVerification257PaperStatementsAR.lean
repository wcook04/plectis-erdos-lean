/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusCriticalCapacityGeometric
import Erdos249257.BooleanMobiusExactRowCrossing
import Erdos249257.BooleanMobiusExactRowDoubling
import Erdos249257.BooleanMobiusGlobalRepair
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.BooleanMobiusSkipRow
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.BooleanMobiusSkippedCoreCriticalCapacity
import Erdos249257.CertificateKernel
import Erdos249257.CofinalStripReturn
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCutLocator
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFatalGapRightTail
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderFloorErrorReset
import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderSkippedRankLimit
import Erdos249257.TerminalOnlyCofinal
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR20.SixMembershipConditions
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusCofinalExactRows`,
`Erdos249257.BooleanMobiusCriticalCapacityCofinal`,
`Erdos249257.BooleanMobiusCriticalCapacityGeometric`,
`Erdos249257.BooleanMobiusExactRowCrossing`, `Erdos249257.BooleanMobiusExactRowDoubling`,
`Erdos249257.BooleanMobiusGlobalRepair`, `Erdos249257.BooleanMobiusLocalRepair`,
`Erdos249257.BooleanMobiusSkipRow`, `Erdos249257.BooleanMobiusSkipRowCofinal`,
`Erdos249257.BooleanMobiusSkippedCoreCriticalCapacity`, `Erdos249257.CertificateKernel`,
`Erdos249257.CofinalStripReturn`, `Erdos249257.DyadicPrefixCompression`,
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.GreedyAchievementSet`,
`Erdos249257.HalfCarryReachability`, `Erdos249257.HalfCutLocator`,
`Erdos249257.HalfCylinderConcreteSeamAdapter`, `Erdos249257.HalfCylinderFatalGapRightTail`,
`Erdos249257.HalfCylinderFiniteShadow`, `Erdos249257.HalfCylinderFloorErrorReset`,
`Erdos249257.HalfCylinderFullShellSeamBridge`,
`Erdos249257.HalfCylinderHalfMembershipClassification`,
`Erdos249257.HalfCylinderIntegerGreedy`, `Erdos249257.HalfCylinderSkippedRankLimit`,
`Erdos249257.TerminalOnlyCofinal`,
`ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity`,
`ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal`,
`ErdosProblems.Erdos257.PaperCompleteR20.SixMembershipConditions`,
`ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels`,
`ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit`,
`ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap`.
-/

open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStatementsAR

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1

noncomputable def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n

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

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def GreedyHalfCarryCofinalStripReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) M ≤
      (halfStripBound (M + 1) : ℤ)

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

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

noncomputable def extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta

noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

noncomputable def terminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) : Bool :=
  b ⟨s - 2, by omega⟩

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)

noncomputable def stemBitsFrom (s : ℕ) (P : Finset ℕ) : ℕ → List Bool
  | d =>
      if h : d < s then
        decide (d ∈ P) :: stemBitsFrom s P (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def stemBits (s : ℕ) (P : Finset ℕ) : List Bool :=
  stemBitsFrom s P 2

noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1

noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n

noncomputable def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)

noncomputable def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)

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

noncomputable def HalfGreedySkippedSeamAlignmentZero : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n) →
      seamIntegerGreedyRemainder n = 0

noncomputable def HalfGreedySkippedSeamEscape : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    halfStripBound (2 * n) < seamIntegerGreedyRemainder n

noncomputable def SeamGreedyCofinalTerminalFalse : Prop :=
  ∃ p : ℕ → ℕ, ∃ hp5 : ∀ j, 5 ≤ p j,
    Tendsto p atTop atTop ∧
      ∀ j, terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false

noncomputable def SeamGreedyEventuallyRight : Prop :=
  ∃ S : ℕ, 5 ≤ S ∧
    ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true

noncomputable def SeamGreedyUnboundedSkippedRanksAlong (rows : ℕ → ℕ) : Prop :=
  ∃ skip : ∀ j, Fin (rows j - 2),
    Tendsto rows atTop atTop ∧
      Tendsto (fun j => ((skip j : ℕ) + 2)) atTop atTop ∧
        ∀ j, seamGreedyWord (rows j) (skip j) = false

noncomputable def SeamGreedyUnboundedTerminalFalse : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧
      terminal (by omega)
        (seamGreedyWord (p + 1)) = false

noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d

noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def exactLocalMersenneRowValue (D : Finset ℕ) : ℝ :=
  ((localMersennePrefixValue D : ℚ) : ℝ)

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)

noncomputable def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d

noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j

noncomputable def localGeometricPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneGeometricQuotient M d

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)

noncomputable def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)

theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) : := @Erdos249257.abs_exactLocalMersenneRowValue_sub_half_le D n hn hD hquot

theorem abs_localMersennePrefixValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) : := @Erdos249257.abs_localMersennePrefixValue_sub_half_le D n hn hD hquot

theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows := @Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply hcap

theorem cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    CofinalExactLocalMersenneHalfRows := @Erdos249257.cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips hskips

theorem eq_halfGreedyPrefixSupport_of_critical_crossing
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) := @Erdos249257.eq_halfGreedyPrefixSupport_of_critical_crossing D c hc hD hbelow hcross

theorem exactLocalMersenneHalfRow_of_positiveHalfGreedySkip
    {c : ℕ} (hc : 4 ≤ c)
    (hpos : 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2) := @Erdos249257.exactLocalMersenneHalfRow_of_positiveHalfGreedySkip c hc hpos hskip

theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ExactLocalMersenneHalfRow (2 * c - 2) := @Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity D c hc hD hbelow hsharp

theorem exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → n < d) ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1 := @Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below D n hn hD htwo hquot hbelow

theorem exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → c < d) ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1 := @Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity D c hc hD hbelow hsharp

theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c)) := @Erdos249257.exists_first_localMersenne_crossing E hE habove

theorem greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
    (n : ℕ) (hn : 3 ≤ n)
    (halign :
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n)) :
    greedyHalfFrozenMargin (n - 1) n =
      -(seamIntegerGreedyRemainder n : ℤ) := @Erdos249257.greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment n hn halign

theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply := @Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix hpre

theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply := @Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake

theorem halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
    {c : ℕ} (hc : 4 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
        (futureSkipCapacity
          (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ) := @Erdos249257.halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage c hc hskip

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
      2 ^ (c - 3) := @Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock c t hc htPos ht hskip htake hfuture hroom

theorem halfGreedy_precriticalSuffix_lt_of_next_skip
    {c : ℕ} (hc : 6 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (hnext : greedyMersenneRemainderRat (1 / 2 : ℚ) c <
      mersenneWeightRat (c + 1)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := @Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip c hc hskip hnext

theorem half_lt_upper_competitor_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hD2 : 2 ≤ D) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    (1 / 2 : ℝ) <
      positiveMersenneSupportValue (↑(insert D u) : Set ℕ) := @Erdos249257.half_lt_upper_competitor_of_eventually_right S D u hS5 hD2 hDS hu hright hbase

theorem half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyCofinalTerminalFalse := @Erdos249257.half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse

theorem half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows := @Erdos249257.half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong

theorem half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ SeamGreedyEventuallyRight := @Erdos249257.half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight

theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse := @Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse

theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_cofinalExactLocalRows hcofinal

theorem half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply hcap

theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative hsign

theorem half_mem_mersenneAchievementSet_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape hescape

theorem localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * n - 1) < 2 ^ (n - 1) := @Erdos249257.localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below D n hn hD htwo hquot hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff D c hc hD hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric D c hc hD hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore D c hc hD hbelow

theorem precriticalCrossingTax_of_futureThreshold
    {D : Finset ℕ} {c t : ℕ}
    (hc : 4 ≤ c)
    (ht : t ≤ c - 3)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localFractionMass (insert c D) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := @Erdos249257.precriticalCrossingTax_of_futureThreshold D c t hc ht hD hres hroom

theorem prefix_add_mersenneTail_lt_half_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D <
      (1 / 2 : ℝ) := @Erdos249257.prefix_add_mersenneTail_lt_half_of_eventually_right S D u hS5 hDS hu hright hbase

theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply := @Erdos249257.skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped

theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative := @Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative

theorem skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    greedyHalfFrozenMargin (n - 1) n < 0 ↔
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
          integerGreedyBits (seamWeights n) (seamSubsetTarget n) ∧
        1 ≤ seamIntegerGreedyRemainder n := @Erdos249257.skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos n hn hskip

theorem unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite :
    SeamGreedyUnboundedTerminalFalse ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := @Erdos249257.unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite

theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2 := @ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core n hn D hD

theorem paper_real_quotient_margins {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) (H : ℝ) :
    ((H+(2*(n : ℝ)+2))/(4 : ℝ)^n < := @ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins n hn D hD H

theorem six_membership_conditions :
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ)) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      (∀ n : ℕ, greedyMersenneRemainder (1/2 : ℝ) n ≤ mersenneTail n) ∧
        ¬ ExistsFatalHalfGap) := @ErdosProblems.Erdos257.PaperCompleteR20.six_membership_conditions

theorem eventually_seamSupport_agrees (K : ℕ) :
    ∀ᶠ s in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ K →
      (d ∈ seamWordSupport (seamGreedyWord s)
        ↔ d ∈ greedyMersenneSupport (1 / 2 : ℝ)) := @ErdosProblems.Erdos257.PaperCompleteR21.eventually_seamSupport_agrees K

theorem paper_both_cofinal_statements_iff_half_membership :
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_both_cofinal_statements_iff_half_membership

theorem paper_capacity_band_exclusion {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D.card ≤ c - 2 ∧ c - 2 ≤ 2 ^ (c - 2) ∧
      (Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3))).card = c - 2 ∧
      (localBinarySuffix D 1 (2 * c - 2) ∉
          Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3)) →
        localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion D c hc hD hbelow hskip

theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix D c hc hD hbelow hcross

theorem paper_exact_row_from_skipped_prefix {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) = 2 ^ (2 * c - 3) - 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix D c hc hD hbelow hskip

theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_row_value_ne_half D h0

theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_not_necessary

theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_suffices_for_sharp_capacity D c hc hD hbelow hcross hfrac

theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band n hn hskip hneg

theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative := @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative hescape

theorem paper_seam_escape_implies_half_membership
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership hescape

end Erdos249257.ExternalVerification257PaperStatementsAR
