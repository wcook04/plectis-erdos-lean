/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.ActualUpperSuccessorCounterexampleEndpoint

namespace Erdos249257.ExternalVerification257ActualUpperSuccessor

open Set
open scoped BigOperators

noncomputable section

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ := seamWeightsFrom s 2

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | w :: ws, b :: bs => (if b then w else 0) + weightedBoolSum ws bs

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def seamGreedyBits (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)

noncomputable def seamGreedyBit (s d : ℕ) : Bool :=
  (seamGreedyBits s).getD (d - 2) false

noncomputable def seamBelowPulse (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if seamGreedyBit s (i + 2) then rowPulse s (i + 2) else 0

structure SeamAdjacentCutView where
  successorCarries : Prop
  belowPulse : ℕ

noncomputable def seamAdjacentCut (s : ℕ) (_hs : 5 ≤ s) : SeamAdjacentCutView where
  successorCarries :=
    (seamGreedyBits (s + 1)).take (s - 2) ≠ seamGreedyBits s
  belowPulse := seamBelowPulse s

noncomputable def affineRightRunCharge (pulse : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * affineRightRunCharge pulse k + pulse k + 4

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

private theorem truncatedMersenneWeight_transport :
    truncatedMersenneWeight =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.truncatedMersenneWeight := rfl

private theorem seamSubsetTarget_transport :
    seamSubsetTarget =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamSubsetTarget := rfl

private theorem rowPulse_transport :
    rowPulse = Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.rowPulse := rfl

private theorem seamWeightsFrom_aux (s : ℕ) : ∀ (k d : ℕ), s - d ≤ k →
    seamWeightsFrom s d =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeightsFrom s d := by
  intro k
  induction k with
  | zero =>
      intro d hd
      have h : ¬ d < s := by omega
      rw [seamWeightsFrom,
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeightsFrom]
      simp [h]
  | succ k ih =>
      intro d hd
      rw [seamWeightsFrom,
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeightsFrom]
      by_cases h : d < s
      · rw [dif_pos h, dif_pos h, ih (d + 1) (by omega)]
        rfl
      · simp [h]

private theorem seamWeightsFrom_transport :
    seamWeightsFrom =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeightsFrom := by
  funext s d
  exact seamWeightsFrom_aux s (s - d) d le_rfl

private theorem seamWeights_transport :
    seamWeights = Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeights := by
  funext s
  simp only [seamWeights,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamWeights,
    seamWeightsFrom_transport]

private theorem integerGreedyBits_transport :
    integerGreedyBits =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits := by
  funext weights C
  induction weights generalizing C with
  | nil =>
      simp [integerGreedyBits,
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits]
  | cons w ws ih =>
      simp [integerGreedyBits,
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits, ih]

private theorem weightedBoolSum_transport :
    weightedBoolSum =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum := by
  funext weights bits
  induction weights generalizing bits with
  | nil =>
      cases bits <;>
        simp [weightedBoolSum,
          Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum]
  | cons w ws ih =>
      cases bits with
      | nil =>
          simp [weightedBoolSum,
            Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum]
      | cons b bs =>
          cases b <;>
            simp [weightedBoolSum,
              Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum, ih]

private theorem integerGreedyRemainder_transport :
    integerGreedyRemainder =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder := by
  funext weights C
  simp only [integerGreedyRemainder,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder,
    weightedBoolSum_transport, integerGreedyBits_transport]

private theorem seamIntegerGreedyRemainder_transport :
    seamIntegerGreedyRemainder =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder := by
  funext s
  simp only [seamIntegerGreedyRemainder,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder,
    integerGreedyRemainder_transport, seamWeights_transport, seamSubsetTarget_transport]

private theorem affineRightRunCharge_transport :
    affineRightRunCharge = Erdos257PeriodNoncollapse.affineRightRunCharge := by
  funext pulse k
  induction k with
  | zero =>
      simp only [affineRightRunCharge, Erdos257PeriodNoncollapse.affineRightRunCharge]
  | succ k ih =>
      simp only [affineRightRunCharge,
        Erdos257PeriodNoncollapse.affineRightRunCharge, ih]

private theorem seamGreedyBits_eq_toList (s : ℕ) :
    seamGreedyBits s =
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s).toList := by
  rw [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord_toList]
  simp only [seamGreedyBits, integerGreedyBits_transport, seamWeights_transport,
    seamSubsetTarget_transport]

private theorem seamGreedyBits_length (s : ℕ) :
    (seamGreedyBits s).length = s - 2 := by
  rw [seamGreedyBits_eq_toList]
  simp [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList]

private theorem seamGreedyBit_eq (s i : ℕ) (hi : i < s - 2) :
    seamGreedyBit s (i + 2) =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s ⟨i, hi⟩ := by
  have hlen : (seamGreedyBits s).length = s - 2 := seamGreedyBits_length s
  rw [seamGreedyBit, Nat.add_sub_cancel,
    List.getD_eq_getElem _ _ (by omega)]
  simp [seamGreedyBits_eq_toList,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList]

private theorem toNatWord_apply (s i : ℕ) (hi : i < s - 2) :
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord
        (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s) (i + 2) =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s ⟨i, hi⟩ := by
  have h2 : 2 ≤ i + 2 := by omega
  have hs : i + 2 < s := by omega
  simp [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, h2, hs]

private theorem belowPulse_transport (s : ℕ) (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).belowPulse =
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).belowPulse := by
  have hbp :
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).belowPulse =
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.wordPulse s
          (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord
            (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s)) := rfl
  rw [hbp]
  simp only [seamAdjacentCut, seamBelowPulse,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.wordPulse]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < s - 2 := Finset.mem_range.mp hi
  rw [seamGreedyBit_eq s i hi', toNatWord_apply s i hi', rowPulse_transport]

private theorem take_toList_extend {s : ℕ} (hs : 3 ≤ s)
    (b : Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord s) (beta : Bool) :
    List.take (s - 2)
        (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList
          (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.extend b beta)) =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList b := by
  refine List.ext_getElem ?_ ?_
  · simp [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList]
    omega
  · intro n h1 h2
    have hn : n < s - 2 := by
      simpa [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList] using h2
    simp only [Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList,
      List.getElem_take, List.getElem_ofFn,
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.extend]
    simp [hn]

private theorem take_seamGreedyBits_succ_iff (s : ℕ) (hs : 5 ≤ s) :
    (seamGreedyBits (s + 1)).take (s - 2) = seamGreedyBits s ↔
      ¬ (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
          s hs).successorCarries := by
  have hbelow :
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below =
        Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s := rfl
  constructor
  · intro h hcarry
    rw [seamGreedyBits_eq_toList, seamGreedyBits_eq_toList,
      Erdos257PeriodNoncollapse.seamGreedyWord_succ_eq_upperBranch
        s hs hcarry,
      take_toList_extend (by omega)] at h
    have habove :
        (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).above =
          Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord s :=
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.toList_injective h
    have hstrict :=
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).above_strict
    have hadm :=
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_admissible
    rw [habove] at hstrict
    rw [hbelow] at hadm
    omega
  · intro hncarry
    obtain ⟨beta, hbeta⟩ :
        ∃ beta : Bool,
          Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamGreedyWord (s + 1) =
            Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.SeamRowWord.extend
              (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
                s hs).below beta := by
      by_cases hmid :
          4 * (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
                s hs).remainder +
              (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamPerturbedFamily
                s (by omega)).gap -
              (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
                s hs).belowPulse <
            (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
              s hs).terminalWeight
      · exact ⟨false,
          Erdos257PeriodNoncollapse.seamGreedyWord_succ_eq_middleBranch
            s hs hncarry hmid⟩
      · exact ⟨true,
          Erdos257PeriodNoncollapse.seamGreedyWord_succ_eq_rightBranch
            s hs hncarry (Nat.le_of_not_lt hmid)⟩
    rw [seamGreedyBits_eq_toList, seamGreedyBits_eq_toList, hbeta,
      take_toList_extend (by omega), hbelow]

private theorem successorCarries_iff (s : ℕ) (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).successorCarries ↔
      (Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.seamAdjacentCut
        s hs).successorCarries := by
  simp only [seamAdjacentCut, ne_eq, take_seamGreedyBits_succ_iff s hs, not_not]

private theorem rightPacket_transport :
    SeamActualUpperRightPacketLinearEscape ↔
      ErdosProblems.Erdos257.SeamActualUpperRightPacketLinearEscape := by
  simp only [SeamActualUpperRightPacketLinearEscape,
    ErdosProblems.Erdos257.SeamActualUpperRightPacketLinearEscape,
    successorCarries_iff, belowPulse_transport,
    seamIntegerGreedyRemainder_transport, affineRightRunCharge_transport]

private theorem successorEscape_transport :
    SeamActualUpperSuccessorLinearEscape ↔
      ErdosProblems.Erdos257.SeamActualUpperSuccessorLinearEscape := by
  simp only [SeamActualUpperSuccessorLinearEscape,
    ErdosProblems.Erdos257.SeamActualUpperSuccessorLinearEscape,
    successorCarries_iff, belowPulse_transport,
    seamIntegerGreedyRemainder_transport]

theorem actualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  rw [rightPacket_transport, successorEscape_transport]
  exact
    ErdosProblems.Erdos257.seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape

theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  rw [successorEscape_transport] at hescape
  rw [show erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries from rfl,
    show UniversalMersenneSubseriesIrrationality =
      ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality from rfl]
  exact
    ErdosProblems.Erdos257.actualUpperSuccessorLinearEscape_completeCounterexample hescape

end

end Erdos249257.ExternalVerification257ActualUpperSuccessor
