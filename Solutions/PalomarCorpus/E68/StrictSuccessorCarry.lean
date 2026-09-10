/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.CompanionOrbitRationality
import Solutions.PalomarCorpus.E68.Shared

namespace PalomarCorpus.E68.StrictSuccessorCarry
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)

noncomputable section

noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

theorem companionOrbit_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  constructor
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      companionConstant, ErdosProblems.Erdos68.companionConstant,
      ErdosProblems.Erdos68.compConstTerm, facFloor,
      ErdosProblems.Erdos68.facFloor] using
      ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      companionConstant, ErdosProblems.Erdos68.companionConstant,
      ErdosProblems.Erdos68.compConstTerm, facFloor,
      ErdosProblems.Erdos68.facFloor] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_companion_floor_misses

theorem strictSuccessorCarry_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_unit_carries
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries
  · intro m hm
    simpa [factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

end

end PalomarCorpus.E68.StrictSuccessorCarry
