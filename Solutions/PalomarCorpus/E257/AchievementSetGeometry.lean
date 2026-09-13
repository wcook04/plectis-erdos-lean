/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import Solutions.PalomarCorpus.E257.Statement

open scoped ENNReal
open Set MeasureTheory

namespace PalomarCorpus.E257.AchievementSetGeometry
export PalomarCorpus.E257.Shared (mersenneWeight positiveMersenneSupportValue)

noncomputable section

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
