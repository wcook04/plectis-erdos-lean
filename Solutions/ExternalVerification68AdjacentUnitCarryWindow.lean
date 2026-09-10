import Mathlib
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow

namespace Erdos249257.ExternalVerification68AdjacentUnitCarryWindow

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1
def factorialGapPrefix (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
def predecessorScaled (m : ℕ) : ℚ := ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)
def predecessorNumerator (m : ℕ) : ℤ := let q := predecessorScaled m; (⌊q⌋ + 1) * q.den - q.num
def transitionNormalizer (m : ℕ) : ℕ := (predecessorScaled m).den * (m.factorial - 1) / (predecessorScaled (m + 1)).den
noncomputable def predecessorGap (m : ℕ) : ℝ := (strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1) : ℝ) - ((m - 1).factorial : ℝ) * (factorialGapPrefix (m - 1) : ℝ)
noncomputable def stepCarry (m : ℕ) : ℤ := -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * predecessorGap m⌋
def windowDen (m : ℕ) : ℤ := ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)
def windowLower (m : ℕ) : ℤ := (m + 2 : ℤ) * windowDen m + (m + 1 : ℤ) * ((predecessorScaled m).den : ℤ) * (((m + 1).factorial : ℤ) - 1) + ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1)
def windowState (m : ℕ) : ℤ := (m : ℤ) * (m + 1 : ℤ) * predecessorNumerator m * ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)
def windowOffset (m : ℕ) : ℤ := windowState m - windowLower m

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

theorem consecutive_unit_carries_iff_positive_offset_le_den {m : ℕ} (hm : 3 ≤ m) :
    (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔
      0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by
  convert ErdosProblems.Erdos68.consecutive_unit_carries_iff_positive_offset_le_den hm
  all_goals try exact stepCarry_fun_eq

theorem twoStep_den_mul_transitionNormalizers {m : ℕ} (hm : 3 ≤ m) :
    (predecessorScaled (m + 2)).den * transitionNormalizer (m + 1) * transitionNormalizer m =
      (predecessorScaled m).den * (m.factorial - 1) * ((m + 1).factorial - 1) := by
  convert ErdosProblems.Erdos68.twoStep_den_mul_transitionNormalizers hm

theorem adjacentUnitCarryWindowDen_eq_twoStep_den {m : ℕ} (hm : 3 ≤ m) :
    windowDen m =
      ((predecessorScaled (m + 2)).den : ℤ) * transitionNormalizer (m + 1) *
        transitionNormalizer m := by
  convert ErdosProblems.Erdos68.adjacentUnitCarryWindowDen_eq_twoStep_den hm

theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization {m : ℕ} (hm : 3 ≤ m) :
    windowOffset m =
      predecessorNumerator (m + 2) * transitionNormalizer (m + 1) * transitionNormalizer m +
        windowDen m *
          (((m + 1 : ℕ) : ℤ) * stepCarry m + stepCarry (m + 1) - (m + 2 : ℤ)) := by
  convert ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset_eq_twoStep_factorization hm
  all_goals try exact stepCarry_fun_eq

end Erdos249257.ExternalVerification68AdjacentUnitCarryWindow
