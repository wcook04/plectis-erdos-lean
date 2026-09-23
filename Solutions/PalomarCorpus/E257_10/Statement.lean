/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFloorErrorReset
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Erdos249257.HalfCylinderSeamLimit
import ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership
import ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit
import ErdosProblems.Erdos257.PaperCompleteR21.UpperResetBandCertificate

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_10

Every non-theorem declaration of `PalomarCorpus/E257_10/Challenge.lean`, verbatim and in
the same order, together with the proof obligations those declarations name, each stated
verbatim from the Challenge and proved in place from the source development that this file
imports for those proofs. The Solution modules import this file instead of re-declaring or
aliasing the definitions, so every constant that Comparator walks from a compared theorem
statement is elaborated from the same text in the same module as in the Challenge.
Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresBL
open Filter
open scoped BigOperators
open Set
open scoped ENNReal
open MeasureTheory
open Topology
/-- Local definition PerturbedFamily, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily (α : Type*) where
  oldSum : α → ℕ
  pulse : α → ℕ
  gap : ℕ
  pulseCap : ℕ
  gap_pos : 0 < gap
  pulse_le : ∀ x, pulse x ≤ pulseCap
  oldSum_injective : Function.Injective oldSum
  separated : ∀ {x y}, oldSum x < oldSum y →
    oldSum x + gap ≤ oldSum y
  pulseCap_lt_three_gap : pulseCap < 3 * gap
/-- Local definition AdjacentCut, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily.AdjacentCut {α : Type*} (F : PerturbedFamily α) (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x
/-- Local definition abovePulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.abovePulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.above
/-- Local definition belowPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.belowPulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.below
/-- Local definition overshoot, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C
/-- Local definition remainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below
/-- Local definition successorCarries, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap
/-- Local definition terminalWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local definition toNatWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Local definition wordWeightSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0
/-- Proof obligation `gap_pos` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_gap_pos (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    0 < gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).gap_pos
/-- Proof obligation `oldSum_injective` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_oldSum_injective (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    Function.Injective oldSum := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).oldSum_injective
/-- Proof obligation `separated` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_separated (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    let gap : ℕ := 2 ^ (s + 1);
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).separated
/-- Proof obligation `pulseCap_lt_three_gap` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_pulseCap_lt_three_gap (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    let pulseCap : ℕ := 2 * (s - 2);
    pulseCap < 3 * gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).pulseCap_lt_three_gap
/-- The quotient pulse contributed by rank d between consecutive seam rows at row s, namely 1 if d divides 2s+2, plus twice 1 if d divides 2s+1, and 0 for the nondividing cases. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- Local definition wordPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.wordPulse_le, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem wordPulse_le (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ 2 * (s - 2) := @Erdos249257.HalfCylinderIntegerGreedy.wordPulse_le s b
/-- Local definition seamPerturbedFamily, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamPerturbedFamily (s : ℕ) (hs : 3 ≤ s) :
    PerturbedFamily (SeamRowWord s) where
  oldSum b := wordWeightSum s b.toNatWord
  pulse b := wordPulse s b.toNatWord
  gap := 2 ^ (s + 1)
  pulseCap := 2 * (s - 2)
  gap_pos := @seamPerturbedFamily_gap_pos s hs
  pulse_le b := wordPulse_le s b.toNatWord
  oldSum_injective := @seamPerturbedFamily_oldSum_injective s hs
  separated := @seamPerturbedFamily_separated s hs
  pulseCap_lt_three_gap := @seamPerturbedFamily_pulseCap_lt_three_gap s hs
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.exists_seamWord_minimal_above, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem exists_seamWord_minimal_above
    {s : ℕ} (hs : 5 ≤ s) :
    ∃ a : SeamRowWord s,
      seamSubsetTarget s <
          (seamPerturbedFamily s (by omega)).oldSum a ∧
        ∀ x : SeamRowWord s,
          seamSubsetTarget s <
              (seamPerturbedFamily s (by omega)).oldSum x →
            (seamPerturbedFamily s (by omega)).oldSum a ≤
              (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.exists_seamWord_minimal_above s hs
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits_length, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits_length weights C
/-- The total weight selected by a Boolean word, namely the sum of those weights whose corresponding entry of the word is true, with the recursion stopping at the end of either list. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- The capacity left unpaid after the greedy Boolean word has been applied to a weight list, namely the capacity minus the weight it selects. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- Local definition seamAboveWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_minimal, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem seamAboveWord_minimal
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum x) :
    (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) ≤
      (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_minimal s hs x hx
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict s hs
/-- The list of truncated Mersenne weights at seam row s for the ranks from the given starting index up to s minus 1, in increasing rank order. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The seam weight list at row s, namely the truncated Mersenne weights for ranks 2 up to s minus 1. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamWeights_length_eq, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.seamWeights_length_eq s
/-- Local definition seamGreedyWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Proof obligation `below_admissible` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_admissible (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    F.oldSum below ≤ C := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_admissible
/-- Proof obligation `below_maximal` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_maximal (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_maximal
/-- The adjacent cut view at seam row s, for s at least 5: its proposition field states that the first s minus 2 bits of the greedy word at row s+1 differ from the greedy word at row s, and its numeric field is the pulse below the seam at row s. -/
noncomputable def seamAdjacentCut (s : ℕ) (hs : 5 ≤ s) :
    (seamPerturbedFamily s (by omega)).AdjacentCut
      (seamSubsetTarget s) where
  below := seamGreedyWord s
  above := seamAboveWord s hs
  below_admissible := @seamAdjacentCut_below_admissible s hs
  below_maximal := @seamAdjacentCut_below_maximal s hs
  above_strict := seamAboveWord_strict hs
  above_minimal := seamAboveWord_minimal hs
/-- The greedy remainder of the seam subset sum problem at row s, namely the seam capacity minus the total weight selected greedily from the seam weight list. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- Local definition seamGreedyNormalizedRemainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyNormalizedRemainder (s : ℕ) : ℝ :=
  (seamIntegerGreedyRemainder s : ℝ) / (4 : ℝ) ^ s
/-- Local definition SeamGreedyRemainderSubquadraticAlong, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyRemainderSubquadraticAlong (rows : ℕ → ℕ) : Prop :=
  Tendsto rows atTop atTop ∧
    Tendsto (fun j => seamGreedyNormalizedRemainder (rows j))
      atTop (nhds 0)
/-- Local definition SeamGreedyUpperOrMiddleAt, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUpperOrMiddleAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries ∨
    (¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight)
/-- Local definition SeamUpperResetDyadicBandEscape, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamUpperResetDyadicBandEscape : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      ∀ j : ℕ, j ≤ d →
        2 ^ (d - j + 1) <
            4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
                (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
            2 ^ (d - j + 1)
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The remainder left by the greedy Mersenne rule applied to a nonnegative real x through rank n: it starts at x and, at each rank n+1, subtracts the weight 1 divided by 2 to the power n+1 minus 1 exactly when that weight is at most the current remainder. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of ranks selected by the greedy Mersenne rule on x, namely the positive m for which the weight at m is at most the greedy remainder after rank m minus 1. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The base two Mersenne achievement set, namely the set of reals of the form sum over a in A of 1 divided by 2 to the power a minus 1, taken over all sets A of positive exponents; equivalently the set of all subsums of the series with terms 1 divided by 2 to the power n minus 1 for n at least 1. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- Local definition seamGreedyFiniteValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyFiniteValue (s : ℕ) : ℝ :=
  positiveMersenneSupportValue
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)
/-- Local definition PaperResetSqrtEscape, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PaperResetSqrtEscape : Prop :=
  ∀ (r : ℕ) (hr5 : 5 ≤ r), 10 ≤ r →
    SeamGreedyUpperOrMiddleAt r hr5 →
      (2 : ℝ) ^ (((r : ℝ) + 5) / 2) <
        |((seamIntegerGreedyRemainder (r + 1) : ℕ) : ℝ) - (2 : ℝ) ^ (r + 1)|
/-- Local definition greedyHalfTargetValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def greedyHalfTargetValue : ℝ :=
  positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ))
/-- Local definition seamGreedyLimitDeficit, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyLimitDeficit : ℝ := 1 / 2 - greedyHalfTargetValue
end PalomarCorpus.E257.PaperStructuresBL
