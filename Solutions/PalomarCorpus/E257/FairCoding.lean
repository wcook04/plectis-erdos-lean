/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperGeometryCompletion.FairCoding
import Solutions.PalomarCorpus.E257.Shared

open Set MeasureTheory Topology
open scoped ENNReal

namespace PalomarCorpus.E257.FairCoding
export PalomarCorpus.E257.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

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
