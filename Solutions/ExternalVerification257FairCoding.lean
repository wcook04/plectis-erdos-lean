import Mathlib
import ErdosProblems.Erdos257.PaperGeometryCompletion.FairCoding

/-!
# Source transport for fair coding of the Mersenne achievement set

The compared statements are transported from
`ErdosProblems.Erdos257.PaperGeometryCompletion.fairCoding_pushforward_eq_volume_restrict`,
`measurePreserving_fairCoding`, and `fairCoding_rational_values_null`.
-/

namespace Erdos249257.ExternalVerification257FairCoding

open Set MeasureTheory Topology
open scoped ENNReal

noncomputable section

abbrev Digits := ℕ → Fin 2

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneDigitTerm (k : ℕ) (b : Digits) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : Digits) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

def fairCoin : Measure (Fin 2) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

def fairDigits : Measure Digits :=
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

end Erdos249257.ExternalVerification257FairCoding
