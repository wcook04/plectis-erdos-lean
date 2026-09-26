/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow
import Solutions.PalomarCorpus.E68_06.Statement

namespace PalomarCorpus.E68.AdjacentUnitCarryWindow
export PalomarCorpus.E68_06.Shared (factorialGapPrefix strictFacTopRat)

lemma factorialGapPrefix_source_eq (n : ℕ) :
    factorialGapPrefix n = ErdosProblems.Erdos68.factorialGapPrefix n := by
  unfold factorialGapPrefix ErdosProblems.Erdos68.factorialGapPrefix
  rfl

lemma strictFacTopRat_source_eq (x : ℚ) (n : ℕ) :
    strictFacTopRat x n = ErdosProblems.Erdos68.strictFacTopRat x n := by
  unfold strictFacTopRat ErdosProblems.Erdos68.strictFacTopRat
  rfl

lemma predecessorGap_source_eq (m : ℕ) :
    predecessorGap m = ErdosProblems.Erdos68.factorialGapPredecessorGap m := by
  unfold predecessorGap ErdosProblems.Erdos68.factorialGapPredecessorGap
  rw [factorialGapPrefix_source_eq, ErdosProblems.Erdos68.strictFacTop_ratCast,
    strictFacTopRat_source_eq]

lemma stepCarry_source_eq (m : ℕ) :
    stepCarry m = ErdosProblems.Erdos68.factorialGapStepCarry m := by
  unfold stepCarry ErdosProblems.Erdos68.factorialGapStepCarry
  rw [predecessorGap_source_eq]

@[simp] lemma stepCarry_fun_eq :
    stepCarry = ErdosProblems.Erdos68.factorialGapStepCarry :=
  funext stepCarry_source_eq

lemma predecessorScaled_source_eq (m : ℕ) :
    predecessorScaled m = ErdosProblems.Erdos68.factorialGapPredecessorScaledRat m := by
  unfold predecessorScaled ErdosProblems.Erdos68.factorialGapPredecessorScaledRat
  simp only [factorialGapPrefix_source_eq]

lemma predecessorNumerator_source_eq (m : ℕ) :
    predecessorNumerator m =
      ErdosProblems.Erdos68.factorialGapPredecessorGapNumerator m := by
  unfold predecessorNumerator ErdosProblems.Erdos68.factorialGapPredecessorGapNumerator
  simp only [predecessorScaled_source_eq]

lemma transitionNormalizer_source_eq (m : ℕ) :
    transitionNormalizer m =
      ErdosProblems.Erdos68.factorialGapPredecessorTransitionNormalizer m := by
  unfold transitionNormalizer ErdosProblems.Erdos68.factorialGapPredecessorTransitionNormalizer
  simp only [predecessorScaled_source_eq]

lemma windowDen_source_eq (m : ℕ) :
    windowDen m = ErdosProblems.Erdos68.adjacentUnitCarryWindowDen m := by
  unfold windowDen ErdosProblems.Erdos68.adjacentUnitCarryWindowDen
  simp only [predecessorScaled_source_eq]

lemma windowLower_source_eq (m : ℕ) :
    windowLower m = ErdosProblems.Erdos68.adjacentUnitCarryWindowLowerNum m := by
  unfold windowLower ErdosProblems.Erdos68.adjacentUnitCarryWindowLowerNum
  simp only [windowDen_source_eq, predecessorScaled_source_eq]

lemma windowState_source_eq (m : ℕ) :
    windowState m = ErdosProblems.Erdos68.adjacentUnitCarryWindowStateNum m := by
  unfold windowState ErdosProblems.Erdos68.adjacentUnitCarryWindowStateNum
  simp only [predecessorNumerator_source_eq]

lemma windowOffset_source_eq (m : ℕ) :
    windowOffset m = ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset m := by
  unfold windowOffset ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset
  simp only [windowState_source_eq, windowLower_source_eq]

theorem consecutive_unit_carries_iff_positive_offset_le_den {m : ℕ} (hm : 3 ≤ m) :
    (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔
      0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by
  simpa only [stepCarry_source_eq, windowOffset_source_eq, windowDen_source_eq] using
    ErdosProblems.Erdos68.consecutive_unit_carries_iff_positive_offset_le_den hm

theorem twoStep_den_mul_transitionNormalizers {m : ℕ} (hm : 3 ≤ m) :
    (predecessorScaled (m + 2)).den * transitionNormalizer (m + 1) * transitionNormalizer m =
      (predecessorScaled m).den * (m.factorial - 1) * ((m + 1).factorial - 1) := by
  simpa only [predecessorScaled_source_eq, transitionNormalizer_source_eq] using
    ErdosProblems.Erdos68.twoStep_den_mul_transitionNormalizers hm

theorem adjacentUnitCarryWindowDen_eq_twoStep_den {m : ℕ} (hm : 3 ≤ m) :
    windowDen m =
      ((predecessorScaled (m + 2)).den : ℤ) * transitionNormalizer (m + 1) *
        transitionNormalizer m := by
  simpa only [windowDen_source_eq, predecessorScaled_source_eq,
    transitionNormalizer_source_eq] using
    ErdosProblems.Erdos68.adjacentUnitCarryWindowDen_eq_twoStep_den hm

theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization {m : ℕ} (hm : 3 ≤ m) :
    windowOffset m =
      predecessorNumerator (m + 2) * transitionNormalizer (m + 1) * transitionNormalizer m +
        windowDen m *
          (((m + 1 : ℕ) : ℤ) * stepCarry m + stepCarry (m + 1) - (m + 2 : ℤ)) := by
  simpa only [windowOffset_source_eq, predecessorNumerator_source_eq,
    transitionNormalizer_source_eq, windowDen_source_eq, stepCarry_source_eq] using
    ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset_eq_twoStep_factorization hm

end PalomarCorpus.E68.AdjacentUnitCarryWindow
