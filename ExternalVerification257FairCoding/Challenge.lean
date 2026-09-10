import Mathlib

/-!
# Trusted challenge for fair coding of the Mersenne achievement set

Fair infinite product measure on binary digit strings is pushed forward by the
positive-index Mersenne coding map onto Lebesgue measure restricted to the
achievement set. The same map is measure-preserving, and the preimage of the
rationals is a null set. These identities do not settle Erdős #257.
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

theorem fairCoding_pushforward_eq_volume_restrict :
    Measure.map positiveMersenneDigitValue fairDigits =
      volume.restrict mersenneAchievementSet := by
  sorry

theorem measurePreserving_fairCoding :
    MeasurePreserving positiveMersenneDigitValue fairDigits
      (volume.restrict mersenneAchievementSet) := by
  sorry

theorem fairCoding_rational_values_null :
    fairDigits
        (positiveMersenneDigitValue ⁻¹' Set.range (fun q : ℚ => (q : ℝ))) =
      0 := by
  sorry

end

end Erdos249257.ExternalVerification257FairCoding
