/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.ActualUpperSuccessorCounterexampleEndpoint
import Solutions.PalomarCorpus.E257.Shared

open Set
open scoped BigOperators

namespace PalomarCorpus.E257.ActualUpperSuccessor
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries integerGreedyBits)

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
    ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
    ErdosProblems.Erdos257.actualUpperSuccessorLinearEscape_completeCounterexample
      hsource

end

end PalomarCorpus.E257.ActualUpperSuccessor
