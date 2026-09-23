/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 6.1 to 6.2: conditional membership tests; exact identities and reductions

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Some theorems below are lemmas or proof fields
that the copied definitions name, and their documentation says so; the papers state none
of them, and the Solution proves each from the source. Erdős problem #257 remains open,
and no theorem in this entry decides it.
-/

open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresCD
open Set
open Filter
open scoped BigOperators
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
/-- Local definition extend, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local definition toNatWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Local definition wordWeightSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0
/-- Proof obligation `gap_pos` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_gap_pos (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    0 < gap := by
  sorry
/-- Proof obligation `oldSum_injective` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_oldSum_injective (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    Function.Injective oldSum := by
  sorry
/-- Proof obligation `separated` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_separated (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    let gap : ℕ := 2 ^ (s + 1);
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := by
  sorry
/-- Proof obligation `pulseCap_lt_three_gap` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_pulseCap_lt_three_gap (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    let pulseCap : ℕ := 2 * (s - 2);
    pulseCap < 3 * gap := by
  sorry
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
    wordPulse s b ≤ 2 * (s - 2) := by
  sorry
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
              (seamPerturbedFamily s (by omega)).oldSum x := by
  sorry
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
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
  sorry
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
      (seamPerturbedFamily s (by omega)).oldSum x := by
  sorry
/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict, which a copied definition cites. It is carried as a statement so that its proof stays in the source development, and the Solution proves it by applying the source lemma. -/
theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) := by
  sorry
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
  sorry
/-- Local definition seamGreedyWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Proof obligation `below_admissible` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_admissible (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    F.oldSum below ≤ C := by
  sorry
/-- Proof obligation `below_maximal` of the local copy of Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own parameter and field values. The definition names this theorem for the field, and the Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_maximal (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := by
  sorry
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
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- Local definition IsLargestFalseRank, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def IsLargestFalseRank {s : ℕ} (b : SeamRowWord s) (d : ℕ) : Prop :=
  2 ≤ d ∧ d < s ∧
    d ∉ seamWordSupport b ∧
      ∀ e : ℕ, d < e → e < s → e ∈ seamWordSupport b
/-- Local definition SeamGreedyUpperOrMiddleAt, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUpperOrMiddleAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries ∨
    (¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight)
/-- Local definition LargestSkipLateStepSocket, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def LargestSkipLateStepSocket : Prop :=
  ∀ (s d : ℕ) (hs : 14 ≤ s),
    IsLargestFalseRank (seamGreedyWord s) d →
      2 * s < 3 * d →
        2 * (s + 1) < 3 * d ∨
          SeamGreedyUpperOrMiddleAt s (by omega)
/-- Local definition SeamGreedyUnboundedUpperOrMiddle, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUnboundedUpperOrMiddle : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧ SeamGreedyUpperOrMiddleAt p hp5
/-- Local definition SeamMiddleProducerCardEscape, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamMiddleProducerCardEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        (seamWordSupport (seamAdjacentCut s hs).below).card +
            (seamAdjacentCut s hs).belowPulse + 5 <
          4 * (seamAdjacentCut s hs).remainder
/-- Local definition SeamMiddleProducerRowEscape, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamMiddleProducerRowEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        s ≤ (seamAdjacentCut s hs).remainder
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
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- Local definition seamWordRationalSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordRationalSum {s : ℕ} (b : SeamRowWord s) : ℚ :=
  finiteErdosSum (seamWordSupport b) 2
/-- Local definition seamWordRationalRemainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordRationalRemainder {s : ℕ} (b : SeamRowWord s) : ℚ :=
  1 / 2 - seamWordRationalSum b
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedUpperOrMiddle := by
  sorry
/-- States thm:largest-skip-late from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:middle-producer-escape from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerCardEscape
    (hcard : SeamMiddleProducerCardEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:middle-producer-escape from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    (hrow : SeamMiddleProducerRowEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:upper-reset-band from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:middle-allright-defect from the long record for Erdős problem #257. Transported from Erdos249257.middleProducer_allRight_forces_rational_skip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem middleProducer_allRight_forces_rational_skip
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    seamWordRationalRemainder (seamGreedyWord D) <
      mersenneWeightRat D := by
  sorry
end PalomarCorpus.E257.PaperStructuresCD
