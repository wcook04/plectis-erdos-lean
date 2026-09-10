/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import ErdosProblems.Erdos257.ActualUpperSuccessorCounterexampleEndpoint
import Erdos257PeriodNoncollapse.BooleanMobiusCarry
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import ErdosProblems.Erdos257.WeightedSupportLimits
import ErdosProblems.Erdos257.PaperGeometryCompletion.FairCoding
import Erdos257PeriodNoncollapse.CertificateKernel
import ErdosProblems.Erdos257.BatchReturnSynthesis
import ErdosProblems.Erdos257.GreedyRepairCriterion
import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticSeparationReturn
import Erdos257PeriodNoncollapse.BooleanMobiusSkipRowCofinal
import Erdos257PeriodNoncollapse.GreedyAchievementSet
import Erdos257PeriodNoncollapse.SublogDivisorCoverage
import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality
import Erdos257PeriodNoncollapse.GreedyTrapDynamics
import ErdosProblems.Erdos257.HalfCounterexampleFrontier
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy
import ErdosProblems.Erdos257.PaperCompleteR8.PositiveCoverReturn

open scoped ENNReal
open Set MeasureTheory
open Set
open scoped BigOperators
open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius
open Filter Topology
open Set MeasureTheory Topology
open Filter Set

namespace PalomarCorpus.E257.Shared
structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d

noncomputable def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

noncomputable def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)

noncomputable def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

noncomputable def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}

noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

end PalomarCorpus.E257.Shared
namespace PalomarCorpus.E257.AchievementSetGeometry
export PalomarCorpus.E257.Shared (mersenneWeight positiveMersenneSupportValue)

open scoped ENNReal

open Set MeasureTheory

noncomputable section

noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
theorem volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
    {J : Set ℕ} (hJ0 : 0 ∉ J) {q : ℚ}
    (hvalue : positiveMersenneSupportValue J = (q : ℝ)) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  have hsrc : Erdos257PeriodNoncollapse.positiveMersenneSupportValue J = (q : ℝ) := by
    first
      | exact hvalue
      | simpa [positiveMersenneSupportValue, mersenneWeight,
          Erdos257PeriodNoncollapse.positiveMersenneSupportValue,
          Erdos257PeriodNoncollapse.mersenneWeight] using hvalue
  first
    | exact ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
        hJ0 hsrc
    | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
        SupportedMersenneDigits, positiveMersenneDigitValue,
        mersenneDigitTerm, mersenneWeight,
        ErdosProblems.Erdos257.supportedMersenneAchievementSet,
        ErdosProblems.Erdos257.supportedMersenneDigitValue,
        ErdosProblems.Erdos257.SupportedMersenneDigits,
        Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
        Erdos257PeriodNoncollapse.mersenneDigitTerm,
        Erdos257PeriodNoncollapse.mersenneWeight] using
        ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
          hJ0 hsrc

theorem supportedMersenneAchievementSet_geometry_and_volume (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) ∧
      IsCompact (supportedMersenneAchievementSet J) ∧
      IsNowhereDense (supportedMersenneAchievementSet J) ∧
      (J.Infinite → Perfect (supportedMersenneAchievementSet J)) ∧
      ((∃ F : Finset ℕ,
          J = (↑F : Set ℕ)ᶜ ∧
            volume (supportedMersenneAchievementSet J) =
              ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
        (Jᶜ.Infinite ∧
          volume (supportedMersenneAchievementSet J) = 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first
      | exact ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J
      | simpa [supportedMersenneDigitValue, SupportedMersenneDigits,
          positiveMersenneDigitValue, mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J
  · first
      | exact ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J
  · first
      | exact ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J
  · intro hJ
    first
      | exact ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ
  · first
      | exact ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J

end

end PalomarCorpus.E257.AchievementSetGeometry

namespace PalomarCorpus.E257.ActualUpperSuccessor
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries integerGreedyBits)

open Set
open scoped BigOperators

noncomputable section

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.truncatedMersenneWeight s d
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamSubsetTarget s
noncomputable def seamWeightsFrom (s : ℕ) (d : ℕ) : List ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeightsFrom s d
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeights s
noncomputable def weightedBoolSum (weights : List ℕ) (bits : List Bool) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum weights bits
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder weights C
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder s
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.rowPulse s d
noncomputable def seamGreedyBits (s : ℕ) : List Bool :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits
    (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeights s)
    (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamSubsetTarget s)
noncomputable def seamGreedyBit (s d : ℕ) : Bool :=
  (seamGreedyBits s).getD (d - 2) false
noncomputable def seamBelowPulse (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if seamGreedyBit s (i + 2) then rowPulse s (i + 2) else 0
structure SeamAdjacentCutView where
  successorCarries : Prop
  belowPulse : ℕ

noncomputable def seamAdjacentCut (s : ℕ) (hs : 5 ≤ s) : SeamAdjacentCutView where
  successorCarries :=
    (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).successorCarries
  belowPulse :=
    (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).belowPulse

noncomputable def affineRightRunCharge (pulse : ℕ → ℕ) (k : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.affineRightRunCharge pulse k
noncomputable def SeamActualUpperRightPacketLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    4 ^ k * (2 * (d + k)) ≤
      seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k
noncomputable def SeamActualUpperSuccessorLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    2 ^ (d + 1) - 2 ^ (d - k + 1) + 2 * (d + k) ≤
      seamIntegerGreedyRemainder (d + 1)
theorem actualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  simpa [SeamActualUpperRightPacketLinearEscape,
    SeamActualUpperSuccessorLinearEscape, seamAdjacentCut,
    seamIntegerGreedyRemainder, affineRightRunCharge] using
    ErdosProblems.Erdos257.seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape

theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  have hsource : ErdosProblems.Erdos257.SeamActualUpperSuccessorLinearEscape := by
    simpa [SeamActualUpperSuccessorLinearEscape, seamAdjacentCut,
      seamIntegerGreedyRemainder] using hescape
  simpa [erdosSupportSeries, UniversalMersenneSubseriesIrrationality,
    ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality] using
    ErdosProblems.Erdos257.actualUpperSuccessorLinearEscape_completeCounterexample
      hsource

end

end PalomarCorpus.E257.ActualUpperSuccessor

namespace PalomarCorpus.E257.BooleanMobiusCarry
export PalomarCorpus.E257.Shared (erdosSupportSeries supportCoeff)

open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius

noncomputable section

noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩

noncomputable def booleanMobiusSupport (f : ArithmeticFunction ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1}

noncomputable def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)
noncomputable def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩
structure BooleanMobiusCarryCertificate
    (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1

noncomputable private def toSourceCertificate
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ}
    (cert : BooleanMobiusCarryCertificate p q U) :
    Erdos257PeriodNoncollapse.BooleanMobiusCarryCertificate p q U where
  initial := cert.initial
  positive := cert.positive
  sqrtBound := cert.sqrtBound
  divisible := cert.divisible
  mobiusBoolean := by
    intro n hn
    simpa [carryQuotientAF, carryQuotient,
      Erdos257PeriodNoncollapse.carryQuotientAF,
      Erdos257PeriodNoncollapse.carryQuotient] using cert.mobiusBoolean n hn
noncomputable private def ofSourceCertificate
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ}
    (cert : Erdos257PeriodNoncollapse.BooleanMobiusCarryCertificate p q U) :
    BooleanMobiusCarryCertificate p q U where
  initial := cert.initial
  positive := cert.positive
  sqrtBound := cert.sqrtBound
  divisible := cert.divisible
  mobiusBoolean := by
    intro n hn
    simpa [carryQuotientAF, carryQuotient,
      Erdos257PeriodNoncollapse.carryQuotientAF,
      Erdos257PeriodNoncollapse.carryQuotient] using cert.mobiusBoolean n hn
theorem exists_booleanMobiusCarry_of_support_fraction
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  have hvalue' : Erdos257PeriodNoncollapse.erdosSupportSeries 2 A =
      (p : ℝ) / (q : ℝ) := by
    simpa [erdosSupportSeries,
      Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue
  obtain ⟨U, cert, hreconstruct⟩ :=
    Erdos257PeriodNoncollapse.exists_booleanMobiusCarry_of_support_fraction
      A hzero hpos p q hq hvalue'
  refine ⟨U, ofSourceCertificate cert, ?_⟩
  simpa [carryQuotientAF, carryQuotient,
    Erdos257PeriodNoncollapse.carryQuotientAF,
    Erdos257PeriodNoncollapse.carryQuotient] using hreconstruct

theorem support_fraction_of_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧ erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  simpa [booleanMobiusSupport, carryQuotientAF, carryQuotient,
    erdosSupportSeries, Erdos257PeriodNoncollapse.booleanMobiusSupport,
    Erdos257PeriodNoncollapse.carryQuotientAF,
    Erdos257PeriodNoncollapse.carryQuotient,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.support_fraction_of_booleanMobiusCarry
        p q hq U (toSourceCertificate cert)

theorem BooleanMobiusCarryCertificate.reconstructsSupport
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ} (hq : 0 < q)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧
      carryQuotientAF q U = supportCoeffAF A ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  simpa [booleanMobiusSupport, carryQuotientAF, carryQuotient,
    supportCoeffAF, supportCoeff, IsTemperedBinaryOrbit,
    erdosSupportSeries, Erdos257PeriodNoncollapse.booleanMobiusSupport,
    Erdos257PeriodNoncollapse.carryQuotientAF,
    Erdos257PeriodNoncollapse.carryQuotient,
    Erdos257PeriodNoncollapse.supportCoeffAF,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.IsTemperedBinaryOrbit,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.BooleanMobiusCarryCertificate.reconstructsSupport
        hq (toSourceCertificate cert)

theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U := by
  constructor
  · intro h
    have hsource : ∃ A : Set ℕ, 0 ∉ A ∧
        (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        Erdos257PeriodNoncollapse.erdosSupportSeries 2 A =
          (p : ℝ) / (q : ℝ) := by
      simpa [erdosSupportSeries,
        Erdos257PeriodNoncollapse.erdosSupportSeries] using h
    obtain ⟨U, cert⟩ :=
      (Erdos257PeriodNoncollapse.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
        p q hq).mp hsource
    exact ⟨U, ofSourceCertificate cert⟩
  · rintro ⟨U, cert⟩
    have hsource :=
      (Erdos257PeriodNoncollapse.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
        p q hq).mpr ⟨U, toSourceCertificate cert⟩
    simpa [erdosSupportSeries,
      Erdos257PeriodNoncollapse.erdosSupportSeries] using hsource

end

end PalomarCorpus.E257.BooleanMobiusCarry

namespace PalomarCorpus.E257.DivisibilityWeightedSupport
export PalomarCorpus.E257.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)

open Set

noncomputable section

noncomputable def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

theorem primeSetPart_eq :
    primeSetPart = ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart := rfl

theorem primeWeightedTerm_eq :
    primeWeightedTerm = ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm := by
  funext b P a
  simp [primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm,
    primeSetPart_eq]

theorem FinitePrimeWeighted_eq :
    FinitePrimeWeighted = ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted := by
  funext b A
  simp [FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted,
    primeWeightedTerm_eq]

theorem DivisibilityWeightedClaim_eq :
    DivisibilityWeightedClaim =
      ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim := by
  unfold DivisibilityWeightedClaim
    ErdosProblems.Erdos257.PaperCompleteR7.DivisibilityWeightedClaim
  rw [FinitePrimeWeighted_eq, erdosSupportSeries_eq]

theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  rw [DivisibilityWeightedClaim_eq]
  exact ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim

end

end PalomarCorpus.E257.DivisibilityWeightedSupport

namespace PalomarCorpus.E257.DyadicObservationSummability

open Filter Topology

noncomputable section

noncomputable def supportObservationMass (A : Set ℕ) (α : ℕ → ℝ) (R : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (Finset.range (R + 1)).filter (fun a => 0 < a ∧ a ∈ A), α a
noncomputable def weightedObservationTerm (A : Set ℕ) (α : ℕ → ℝ) (a : ℕ) : ℝ := by
  classical
  exact if 0 < a ∧ a ∈ A then α a / a else 0
theorem supportObservationMass_eq :
    supportObservationMass = ErdosProblems.Erdos257.supportObservationMass :=
  rfl

theorem weightedObservationTerm_eq :
    weightedObservationTerm = ErdosProblems.Erdos257.weightedObservationTerm :=
  rfl

theorem dyadic_supportObservationMass_sum_le (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (J : Finset ℕ) (Q : ℕ) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j * supportObservationMass A α (Q * 2 ^ j)) ≤
      2 * (Q : ℝ) * ∑' a : ℕ, weightedObservationTerm A α a := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq, weightedObservationTerm_eq]
  exact ErdosProblems.Erdos257.dyadic_supportObservationMass_sum_le A α hα hs' J Q

theorem summable_dyadic_supportObservationMass (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j *
      supportObservationMass A α (Q * 2 ^ j)) := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq]
  exact ErdosProblems.Erdos257.summable_dyadic_supportObservationMass A α hα hs' Q

theorem tendsto_dyadic_supportObservationMass_mean (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M) atTop (nhds 0) := by
  have hs' : Summable (ErdosProblems.Erdos257.weightedObservationTerm A α) := by
    rw [weightedObservationTerm_eq] at hs
    exact hs
  rw [supportObservationMass_eq]
  exact ErdosProblems.Erdos257.tendsto_dyadic_supportObservationMass_mean A α hα hs' Q

end

end PalomarCorpus.E257.DyadicObservationSummability

namespace PalomarCorpus.E257.FairCoding
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

open Set MeasureTheory Topology
open scoped ENNReal

noncomputable section

noncomputable abbrev Digits := ℕ → Fin 2
noncomputable def mersenneDigitTerm (k : ℕ) (b : Digits) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : Digits) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

noncomputable def fairCoin : Measure (Fin 2) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1
noncomputable def fairDigits : Measure Digits :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)
theorem mersenneWeight_eq :
    mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight :=
  rfl

theorem mersenneDigitTerm_eq :
    mersenneDigitTerm = Erdos257PeriodNoncollapse.mersenneDigitTerm := by
  funext k b
  simp only [mersenneDigitTerm, Erdos257PeriodNoncollapse.mersenneDigitTerm,
    mersenneWeight_eq]

theorem positiveMersenneDigitValue_eq :
    positiveMersenneDigitValue =
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue := by
  funext b
  simp only [positiveMersenneDigitValue,
    Erdos257PeriodNoncollapse.positiveMersenneDigitValue, mersenneDigitTerm_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue =
      Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem fairCoin_eq :
    fairCoin = ErdosProblems.Erdos257.PaperGeometryCompletion.fairCoin :=
  rfl

theorem fairDigits_eq :
    fairDigits = ErdosProblems.Erdos257.PaperGeometryCompletion.fairDigits := by
  unfold fairDigits ErdosProblems.Erdos257.PaperGeometryCompletion.fairDigits
  rw [fairCoin_eq]

theorem fairCoding_pushforward_eq_volume_restrict :
    Measure.map positiveMersenneDigitValue fairDigits =
      volume.restrict mersenneAchievementSet := by
  rw [positiveMersenneDigitValue_eq, fairDigits_eq, mersenneAchievementSet_eq]
  exact ErdosProblems.Erdos257.PaperGeometryCompletion.fairCoding_pushforward_eq_volume_restrict

theorem measurePreserving_fairCoding :
    MeasurePreserving positiveMersenneDigitValue fairDigits
      (volume.restrict mersenneAchievementSet) := by
  rw [positiveMersenneDigitValue_eq, fairDigits_eq, mersenneAchievementSet_eq]
  exact ErdosProblems.Erdos257.PaperGeometryCompletion.measurePreserving_fairCoding

theorem fairCoding_rational_values_null :
    fairDigits
        (positiveMersenneDigitValue ⁻¹' Set.range (fun q : ℚ => (q : ℝ))) =
      0 := by
  rw [positiveMersenneDigitValue_eq, fairDigits_eq]
  exact ErdosProblems.Erdos257.PaperGeometryCompletion.fairCoding_rational_values_null

end

end PalomarCorpus.E257.FairCoding

namespace PalomarCorpus.E257.FinitePeriodNoncollapse

noncomputable def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)
theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  have hcop : Nat.Coprime b (finiteErdosSum F b).den := by
    simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.coprime_base_den_finiteErdosSum
        F b h0 hb
  refine ⟨hcop, ?_⟩
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.finite_period_noncollapse_rat_den
        F b hF h0 hb

theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.lcm_lt_den_finiteErdosSum
        F b hF h0 hb h2

end PalomarCorpus.E257.FinitePeriodNoncollapse

namespace PalomarCorpus.E257.FourNinthsRepairWindows
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)

open Set

noncomputable section

noncomputable def fourNinthsBinaryFloor (N : ℕ) : ℕ :=
  4 * 2 ^ N / 9
noncomputable def fourNinthsGreedyDefect (N : ℕ) : ℕ :=
  fourNinthsBinaryFloor N -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ))) N

noncomputable def FourNinthsOneStepRepairSucc (N : ℕ) : Prop :=
  (fourNinthsGreedyDefect (N + 1) : ℤ) ≤ (fourNinthsGreedyDefect N : ℤ)
noncomputable def FourNinthsOneStepRepairCofinal : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ FourNinthsOneStepRepairSucc N
theorem mersenneWeight_eq : mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight := rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem supportCoeff_eq : supportCoeff = Erdos257PeriodNoncollapse.supportCoeff := rfl

theorem binaryCoeffPrefixNumerator_eq :
    binaryCoeffPrefixNumerator = Erdos257PeriodNoncollapse.binaryCoeffPrefixNumerator := by
  funext c N
  induction N with
  | zero => rfl
  | succ N ih =>
    show 2 * binaryCoeffPrefixNumerator c N + c (N + 1) = _
    rw [ih]
    rfl

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue = Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem fourNinthsBinaryFloor_eq :
    fourNinthsBinaryFloor = ErdosProblems.Erdos257.fourNinthsBinaryFloor := rfl

theorem fourNinthsGreedyDefect_eq :
    fourNinthsGreedyDefect = ErdosProblems.Erdos257.fourNinthsGreedyDefect := by
  funext N
  simp only [fourNinthsGreedyDefect, ErdosProblems.Erdos257.fourNinthsGreedyDefect,
    fourNinthsBinaryFloor_eq, greedyMersenneSupport_eq, supportCoeff_eq,
    binaryCoeffPrefixNumerator_eq]

theorem FourNinthsOneStepRepairSucc_eq :
    FourNinthsOneStepRepairSucc = ErdosProblems.Erdos257.FourNinthsOneStepRepairSucc := by
  funext N
  simp only [FourNinthsOneStepRepairSucc, ErdosProblems.Erdos257.FourNinthsOneStepRepairSucc,
    fourNinthsGreedyDefect_eq]

theorem FourNinthsOneStepRepairCofinal_eq :
    FourNinthsOneStepRepairCofinal = ErdosProblems.Erdos257.FourNinthsOneStepRepairCofinal := by
  unfold FourNinthsOneStepRepairCofinal ErdosProblems.Erdos257.FourNinthsOneStepRepairCofinal
  rw [FourNinthsOneStepRepairSucc_eq]

theorem exists_repair_in_sqrt_window
    (Q : ℕ → ℕ)
    (hQ : ∀ N, (Q N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4)
    (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧ Q (N + 1) ≤ Q N :=
  ErdosProblems.Erdos257.exists_repair_in_sqrt_window Q hQ K

theorem four_ninths_mem_iff_repairCofinal :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔ FourNinthsOneStepRepairCofinal := by
  rw [mersenneAchievementSet_eq, FourNinthsOneStepRepairCofinal_eq]
  exact ErdosProblems.Erdos257.four_ninths_mem_iff_repairCofinal

theorem four_ninths_mem_iff_repair_sqrt_windows :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        FourNinthsOneStepRepairSucc N := by
  rw [mersenneAchievementSet_eq, FourNinthsOneStepRepairSucc_eq]
  exact ErdosProblems.Erdos257.four_ninths_mem_iff_repair_sqrt_windows

theorem four_ninths_not_mem_of_strict_sqrt_window
    (K : ℕ)
    (h : ∀ N, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      fourNinthsGreedyDefect N < fourNinthsGreedyDefect (N + 1)) :
    (4 / 9 : ℝ) ∉ mersenneAchievementSet := by
  rw [mersenneAchievementSet_eq]
  apply ErdosProblems.Erdos257.four_ninths_not_mem_of_strict_sqrt_window K
  intro N hKN hN
  simpa [fourNinthsGreedyDefect_eq] using h N hKN hN

end

end PalomarCorpus.E257.FourNinthsRepairWindows

namespace PalomarCorpus.E257.GeneralRepairCriterion
export PalomarCorpus.E257.Shared (binaryCoeffPrefixNumerator greedyMersenneRemainder greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)

open Set

noncomputable section

noncomputable def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N

theorem mersenneWeight_eq : mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight := rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem supportCoeff_eq : supportCoeff = Erdos257PeriodNoncollapse.supportCoeff := rfl

theorem binaryCoeffPrefixNumerator_eq :
    binaryCoeffPrefixNumerator = Erdos257PeriodNoncollapse.binaryCoeffPrefixNumerator := by
  funext c N
  induction N with
  | zero => rfl
  | succ N ih =>
    show 2 * binaryCoeffPrefixNumerator c N + c (N + 1) = _
    rw [ih]
    rfl

theorem greedyBinaryDefect_eq :
    greedyBinaryDefect = ErdosProblems.Erdos257.greedyBinaryDefect := by
  funext x N
  simp only [greedyBinaryDefect, ErdosProblems.Erdos257.greedyBinaryDefect,
    greedyMersenneSupport_eq, supportCoeff_eq, binaryCoeffPrefixNumerator_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue = Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

/-- Membership is cofinal non-increase of the greedy defect. -/
theorem mem_iff_greedyBinaryDefect_cofinal_repairs {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_cofinal_repairs hx

/-- The same criterion inside every window of width `2*sqrt K + 12`. -/
theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows hx

end

end PalomarCorpus.E257.GeneralRepairCriterion

namespace PalomarCorpus.E257.LiteralWeightedCover
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)

open Set

noncomputable section

structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

theorem primeSetPart_eq :
    primeSetPart = ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart := rfl

theorem primeWeightedTerm_eq :
    primeWeightedTerm = ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm := by
  funext b P a
  simp [primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm,
    primeSetPart_eq]

theorem FinitePrimeWeighted_eq :
    FinitePrimeWeighted = ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted := by
  funext b A
  simp [FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted,
    primeWeightedTerm_eq]

noncomputable def PositiveCoverData.toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
noncomputable def PositiveCoverData.ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
theorem PositiveCoverData.host_toSource (C : PositiveCoverData) :
    C.host = C.toSource.host := rfl

theorem PositiveCoverData.cost_toSource (C : PositiveCoverData) :
    C.cost = C.toSource.cost := rfl

theorem PositiveCoverData.exponent_toSource (C : PositiveCoverData) :
    C.exponent = C.toSource.exponent := rfl

theorem PositiveCoverData.StrengthenedCostSummable_toSource (C : PositiveCoverData) :
    C.StrengthenedCostSummable ↔ C.toSource.StrengthenedCostSummable := by
  unfold PositiveCoverData.StrengthenedCostSummable
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.StrengthenedCostSummable
  rw [PositiveCoverData.cost_toSource, PositiveCoverData.exponent_toSource]

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData.ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem HasStrengthenedPositiveCover_iff (A : Set ℕ) :
    HasStrengthenedPositiveCover A ↔
      ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover A := by
  constructor
  · rintro ⟨C, hA, hC⟩
    refine ⟨C.toSource, ?_, (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC⟩
    simpa [PositiveCoverData.host_toSource] using hA
  · rintro ⟨C, hA, hC⟩
    refine ⟨PositiveCoverData.ofSource C, ?_,
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC⟩
    simpa [PositiveCoverData.host] using hA

noncomputable def LogBudgetCover.toSource {A : Set ℕ} (C : LogBudgetCover A) :
    ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A where
  frame := C.frame
  weight := C.weight
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := C.weight_positive
  weight_sum := C.weight_sum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := C.covers
  majorises := C.majorises
  budget_summable := C.budget_summable
noncomputable def LogBudgetCover.ofSource {A : Set ℕ}
    (C : ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) :
    LogBudgetCover A where
  frame := C.frame
  weight := C.weight
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := C.weight_positive
  weight_sum := C.weight_sum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := C.covers
  majorises := C.majorises
  budget_summable := C.budget_summable
theorem isEmpty_logBudgetCover_iff (A : Set ℕ) :
    IsEmpty (LogBudgetCover A) ↔
      IsEmpty (ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover A) := by
  constructor
  · intro h
    exact ⟨fun C => (h.elim (LogBudgetCover.ofSource C))⟩
  · intro h
    exact ⟨fun C => (h.elim (C.toSource))⟩

theorem exists_weighted_not_strengthened_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      ¬ HasStrengthenedPositiveCover A ∧ IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hrec, hncover, hn, hirr⟩ :=
    ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_not_strengthened_host
  refine ⟨A, hinf, hzero, ?_, hrec, ?_, ?_, ?_⟩
  · simpa [FinitePrimeWeighted_eq] using hw
  · intro hA
    exact hncover ((HasStrengthenedPositiveCover_iff A).mp hA)
  · exact (isEmpty_logBudgetCover_iff A).mpr hn
  · intro B hBA hBinf b hb
    simpa [erdosSupportSeries_eq] using hirr B hBA hBinf b hb

theorem exists_weighted_obstruction_with_mixed_heredity :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ V : Set ℕ, HasStrengthenedPositiveCover V →
        ∀ B : Set ℕ, B ⊆ A ∪ V → B.Infinite → ∀ b : ℕ, 2 ≤ b →
          Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hn, hmix⟩ :=
    ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_obstruction_with_mixed_heredity
  refine ⟨A, hinf, hzero, ?_, (isEmpty_logBudgetCover_iff A).mpr hn, ?_⟩
  · simpa [FinitePrimeWeighted_eq] using hw
  · intro V hV B hB hBi b hb
    have hV' : ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mp hV
    simpa [erdosSupportSeries_eq] using hmix V hV' B hB hBi b hb

end

end PalomarCorpus.E257.LiteralWeightedCover

namespace PalomarCorpus.E257.MixedWeightedCover
export PalomarCorpus.E257.Shared (FinitePrimeWeighted HasStrengthenedPositiveCover PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)

open Set

noncomputable section

noncomputable def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

theorem primeSetPart_eq :
    primeSetPart = ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart := rfl

theorem primeWeightedTerm_eq :
    primeWeightedTerm = ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm := by
  funext b P a
  simp [primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm,
    primeSetPart_eq]

theorem FinitePrimeWeighted_eq :
    FinitePrimeWeighted = ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted := by
  funext b A
  simp [FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted,
    primeWeightedTerm_eq]

noncomputable def PositiveCoverData.toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
noncomputable def PositiveCoverData.ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
theorem PositiveCoverData.host_toSource (C : PositiveCoverData) :
    C.host = C.toSource.host := rfl

theorem PositiveCoverData.cost_toSource (C : PositiveCoverData) :
    C.cost = C.toSource.cost := rfl

theorem PositiveCoverData.exponent_toSource (C : PositiveCoverData) :
    C.exponent = C.toSource.exponent := rfl

theorem PositiveCoverData.StrengthenedCostSummable_toSource (C : PositiveCoverData) :
    C.StrengthenedCostSummable ↔ C.toSource.StrengthenedCostSummable := by
  unfold PositiveCoverData.StrengthenedCostSummable
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.StrengthenedCostSummable
  rw [PositiveCoverData.cost_toSource, PositiveCoverData.exponent_toSource]

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData.ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem HasStrengthenedPositiveCover_iff (A : Set ℕ) :
    HasStrengthenedPositiveCover A ↔
      ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover A := by
  constructor
  · rintro ⟨C, hA, hC⟩
    refine ⟨C.toSource, ?_, ?_⟩
    · simpa [PositiveCoverData.host_toSource] using hA
    · exact (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC
  · rintro ⟨C, hA, hC⟩
    refine ⟨PositiveCoverData.ofSource C, ?_,
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC⟩
    simpa [PositiveCoverData.host] using hA

theorem MixedSupportClaim_eq :
    MixedSupportClaim ↔ ErdosProblems.Erdos257.PaperCompleteR7.MixedSupportClaim := by
  constructor
  · intro h E V hE0 hE hV A hA hInf b hb
    have hE' : FinitePrimeWeighted 2 E := by
      simpa [FinitePrimeWeighted_eq] using hE
    have hV' : HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mpr hV
    have := h E V hE0 hE' hV' A hA hInf b hb
    simpa [erdosSupportSeries_eq] using this
  · intro h E V hE0 hE hV A hA hInf b hb
    have hE' : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 E := by
      simpa [FinitePrimeWeighted_eq] using hE
    have hV' : ErdosProblems.Erdos257.PaperCompleteR7.HasStrengthenedPositiveCover V :=
      (HasStrengthenedPositiveCover_iff V).mp hV
    have := h E V hE0 hE' hV' A hA hInf b hb
    simpa [erdosSupportSeries_eq] using this

theorem mixedSupportClaim : MixedSupportClaim :=
  MixedSupportClaim_eq.mpr ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim

end

end PalomarCorpus.E257.MixedWeightedCover

namespace PalomarCorpus.E257.PositiveSkipEquivalence
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)

open Set

noncomputable section

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ :=
  Erdos257PeriodNoncollapse.greedyMersenneRemainderRat x
noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c
theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  change 0 < Erdos257PeriodNoncollapse.greedyMersenneRemainderRat
    (1 / 2 : ℚ) n
  exact Erdos257PeriodNoncollapse.greedyMersenneRemainderRat_half_pos n

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  change Erdos257PeriodNoncollapse.CofinalPositiveHalfGreedySkips ↔
    (1 / 2 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet
  exact Erdos257PeriodNoncollapse.cofinalPositiveHalfGreedySkips_iff_half_mem

end

end PalomarCorpus.E257.PositiveSkipEquivalence

namespace PalomarCorpus.E257.RationalMembership
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

open Set

noncomputable section

theorem mersenneWeight_eq :
    mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight :=
  rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem greedyMersenneSkippedSupport_eq :
    greedyMersenneSkippedSupport =
      Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport := by
  funext x
  simp only [greedyMersenneSkippedSupport,
    Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport,
    greedyMersenneSupport_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue =
      Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem greedyMersenneSkippedSupport_infinite_iff_cofinal_skips (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  rw [greedyMersenneSkippedSupport_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport_infinite_iff_cofinal_skips x

theorem infinite_greedyMersenneSkippedSupport_of_rat_mem
    {q : ℚ} (hmem : (q : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq] at hmem
  rw [greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.infinite_greedyMersenneSkippedSupport_of_rat_mem hmem

theorem rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq, greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    q hq

theorem rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (q : ℝ) n := by
  rw [mersenneAchievementSet_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    q hq

end

end PalomarCorpus.E257.RationalMembership

namespace PalomarCorpus.E257.RationalTailRigidity
export PalomarCorpus.E257.Shared (erdosSupportSeries supportCoeff)

open Filter Set

noncomputable section

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0
noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a

noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ :=
  orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd))

theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  simpa [supportCoeff, erdosSupportSeries, binaryCoeffTail,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries,
    Erdos257PeriodNoncollapse.binaryCoeffTail] using
      Erdos257PeriodNoncollapse.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
        A hAinf p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  simpa [SupportCoeffZeroWindow, CoeffZeroWindow, supportCoeff,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.SupportCoeffZeroWindow,
    Erdos257PeriodNoncollapse.CoeffZeroWindow,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.supportCoeffZeroWindow_length_le_eps_logb_add
        A hA p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue) ε hε

theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, oddDoublingOrder,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.oddDoublingOrder,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.one_div_oddOrder_le_reciprocalMass_of_support_fraction
        A hA (by
          simpa [reciprocalSupportTerm,
            Erdos257PeriodNoncollapse.reciprocalSupportTerm] using hsum)
        p c hv hvodd hpv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
        A hAinf p c (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

end

end PalomarCorpus.E257.RationalTailRigidity

namespace PalomarCorpus.E257.ReciprocalSupport

noncomputable section

noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) :
    Irrational (supportPowerSeries b A) := by
  simpa [supportReciprocalTerm, supportPowerSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
    Erdos257PeriodNoncollapse.irrational_erdosSupportSeries_of_summable_reciprocal
      b A hb hA hsum

end

end PalomarCorpus.E257.ReciprocalSupport

namespace PalomarCorpus.E257.ScaledGreedyTrap
export PalomarCorpus.E257.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

open Set
open Filter Topology
open scoped BigOperators

noncomputable section

noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.scaledGreedyRemainder x N
noncomputable def mersenneScale (n : ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.mersenneScale n
noncomputable def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally x
noncomputable def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded x
theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  change Tendsto
    (fun N : ℕ => Erdos257PeriodNoncollapse.scaledGreedyRemainder x N) atTop atTop
  exact Erdos257PeriodNoncollapse.scaledGreedyRemainder_tendsto_atTop_of_not_mem hx hnot

theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  change x ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded x
  exact Erdos257PeriodNoncollapse.mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx

theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  change Erdos257PeriodNoncollapse.mersenneAchievementSet =
    {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ,
      Erdos257PeriodNoncollapse.scaledGreedyRemainder x N < 2}
  exact Erdos257PeriodNoncollapse.mersenneAchievementSet_eq_scaledGreedyTrap

theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  change (q : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally (q : ℝ)
  exact
    Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
      q hq

theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ)
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledLowerBranchCofinally

theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ)
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded

end

end PalomarCorpus.E257.ScaledGreedyTrap

namespace PalomarCorpus.E257.TerminalScaledVanishing
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries supportCoeff)

open Filter Set

noncomputable section

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ :=
  Erdos257PeriodNoncollapse.affineBinaryOrbit a u0
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  Erdos257PeriodNoncollapse.HalfCarryReachability.integerHalfCarry A

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  Erdos257PeriodNoncollapse.HalfCarryReachability.wordSupport a
structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ depth n)
      atTop (nhds 0)

theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  let S' :
      Erdos257PeriodNoncollapse.HalfCarryReachability.HalfTerminalOnlyScaledVanishingSequence :=
    { depth := S.depth
      word := S.word
      depth_pos := S.depth_pos
      depth_tendsto := S.depth_tendsto
      zero := S.zero
      one := S.one
      carry_scaled_tendsto := by
        simpa [integerHalfCarry, wordSupport] using
          S.carry_scaled_tendsto }
  constructor
  · simpa [erdosSupportSeries] using
      ErdosProblems.Erdos257.exists_rational_half_counterexample_of_terminalScaledVanishing
        S'
  · simpa [UniversalMersenneSubseriesIrrationality, erdosSupportSeries,
      ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality] using
      ErdosProblems.Erdos257.not_universal_of_terminalScaledVanishing S'

end

end PalomarCorpus.E257.TerminalScaledVanishing

namespace PalomarCorpus.E257.TwentyOneFatalBranch
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport integerGreedyBits mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)

noncomputable section

noncomputable abbrev mersenneTail := Erdos257PeriodNoncollapse.mersenneTail
noncomputable abbrev GreedyMersenneFatalAt := Erdos257PeriodNoncollapse.GreedyMersenneFatalAt
noncomputable abbrev weightedBoolSum :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum
noncomputable abbrev integerGreedyRemainder :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder
noncomputable abbrev localMersenneQuotient := Erdos257PeriodNoncollapse.localMersenneQuotient
noncomputable abbrev localPrefixQuotient := Erdos257PeriodNoncollapse.localPrefixQuotient
noncomputable abbrev endpointDivisorContribution :=
  Erdos257PeriodNoncollapse.endpointDivisorContribution
noncomputable abbrev localMersenneWeightsFrom :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom
noncomputable abbrev localMersenneWeights :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeights
noncomputable abbrev lowerSupportFromBits :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits
noncomputable abbrev twentyOneQuotientTarget := Erdos257PeriodNoncollapse.twentyOneQuotientTarget
noncomputable abbrev rationalMersenneGreedyBitsFrom :=
  Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom
noncomputable abbrev twentyOneEvenQuotientGreedySupport :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedySupport
noncomputable abbrev twentyOneEvenQuotientGreedyRemainder :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedyRemainder
noncomputable abbrev localPrefixTwoStepPulse := Erdos257PeriodNoncollapse.localPrefixTwoStepPulse
noncomputable abbrev twentyOneTargetTwoStepPulse :=
  Erdos257PeriodNoncollapse.twentyOneTargetTwoStepPulse
noncomputable abbrev TwentyOneClosedLowerStateSupply :=
  Erdos257PeriodNoncollapse.TwentyOneClosedLowerStateSupply
noncomputable abbrev TwentyOneGreedyEventuallyHitsDoublingBlocks :=
  Erdos257PeriodNoncollapse.TwentyOneGreedyEventuallyHitsDoublingBlocks
noncomputable abbrev TwentyOneFatalAlignedBranch :=
  Erdos257PeriodNoncollapse.TwentyOneFatalAlignedBranch
theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen : bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits = integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R :=
  Erdos257PeriodNoncollapse.twentyOneClosedRow_forces_quotientGreedy
    hlen hrow hclosed

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  Erdos257PeriodNoncollapse.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    hsupply

theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch :=
  Erdos257PeriodNoncollapse.one_div_twenty_one_mem_iff_not_fatalAlignedBranch

theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R :=
  Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    hbranch

theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) :=
  Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    hbranch

end

end PalomarCorpus.E257.TwentyOneFatalBranch

namespace PalomarCorpus.E257.VariableExponentCover
export PalomarCorpus.E257.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)

open Set

noncomputable section

noncomputable def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
theorem erdosSupportSeries_eq :
    erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries := rfl

noncomputable def PositiveCoverData.toSource (C : PositiveCoverData) :
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
noncomputable def PositiveCoverData.ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises
theorem PositiveCoverData.host_toSource (C : PositiveCoverData) :
    C.host = C.toSource.host := rfl

theorem PositiveCoverData.cost_toSource (C : PositiveCoverData) :
    C.cost = C.toSource.cost := rfl

theorem PositiveCoverData.exponent_toSource (C : PositiveCoverData) :
    C.exponent = C.toSource.exponent := rfl

theorem PositiveCoverData.StrengthenedCostSummable_toSource (C : PositiveCoverData) :
    C.StrengthenedCostSummable ↔ C.toSource.StrengthenedCostSummable := by
  unfold PositiveCoverData.StrengthenedCostSummable
    ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.StrengthenedCostSummable
  rw [PositiveCoverData.cost_toSource, PositiveCoverData.exponent_toSource]

theorem PositiveCoverData.host_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData.ofSource C).host = C.host := rfl

theorem PositiveCoverData.StrengthenedCostSummable_ofSource
    (C : ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData) :
    (PositiveCoverData.ofSource C).StrengthenedCostSummable ↔
      C.StrengthenedCostSummable := Iff.rfl

theorem StrengthenedPositiveCoverClaim_iff :
    StrengthenedPositiveCoverClaim ↔
      ErdosProblems.Erdos257.PaperCompleteR7.StrengthenedPositiveCoverClaim := by
  constructor
  · intro h C hC A hA hInf b hb
    have hC' : (PositiveCoverData.ofSource C).StrengthenedCostSummable :=
      (PositiveCoverData.StrengthenedCostSummable_ofSource C).mpr hC
    have hA' : A ⊆ (PositiveCoverData.ofSource C).host := by
      simpa [PositiveCoverData.host_ofSource] using hA
    have := h (PositiveCoverData.ofSource C) hC' A hA' hInf b hb
    simpa [erdosSupportSeries_eq] using this
  · intro h C hC A hA hInf b hb
    have hC' : C.toSource.StrengthenedCostSummable :=
      (PositiveCoverData.StrengthenedCostSummable_toSource C).mp hC
    have hA' : A ⊆ C.toSource.host := by
      simpa [PositiveCoverData.host_toSource] using hA
    have := h C.toSource hC' A hA' hInf b hb
    simpa [erdosSupportSeries_eq] using this

theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim :=
  StrengthenedPositiveCoverClaim_iff.mpr
    ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim

end

end PalomarCorpus.E257.VariableExponentCover
