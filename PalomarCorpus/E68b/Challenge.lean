/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #68, band b

Erdős problem #68 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E68` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
/-- The least common multiple of the channel moduli through `D`. Local copy of Erdos68.channelLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The integer numerator of the `d`-th divisor channel. Local copy of Erdos68.channelNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- Factorial-weighted sum of a finite coefficient family. Local copy of Erdos68.factorialMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
/-- Coefficients `(p,-1)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ :=
  ![(p : ℤ), -1]
/-- Support indices `(p-1,p)` of the prime-pair translator. Local copy of Erdos68.primeTranslatorIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ :=
  ![p - 1, p]
/-- The exact rational prefix of the Erdős #68 series through index `n`. Local copy of ErdosProblems.Erdos68.factorialGapPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Strict successor of the factorially scaled prefix. Local copy of ErdosProblems.Erdos68.strictFacTop, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- Distance from the strict factorial successor of the preceding actual prefix to that scaled prefix. Unlike an ordinary fractional-part complement, this takes the value one when the scaled prefix is integral. Local copy of ErdosProblems.Erdos68.factorialGapPredecessorGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
/-- The exact rounding carry in the strict-successor recurrence for the Erdős #68 prefixes. Local copy of ErdosProblems.Erdos68.factorialGapStepCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
/-- States long68:res:translator from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.prime_channel_corrector in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    factorialMoment (primeTranslatorCoeff p)
      (primeTranslatorIndex p) = 0 ∧
    channelNumerator (primeTranslatorCoeff p)
      (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      channelNumerator (primeTranslatorCoeff p)
        (primeTranslatorIndex p) d = 0) := by
  sorry
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.radius_no_eventual_ratio_upper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := by
  sorry
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.radius_not_littleO in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := by
  sorry
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.square_subsequence_radius in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  sorry
/-- States long68:eq:carry-rationality, long68:eq:strict-misses, long68:eq:unit-window from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.strict_successor_characterisation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem strict_successor_characterisation :
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
      ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
        1 + 1 / ((m.factorial : ℝ) - 1) <
            (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
            2 + 1 / ((m.factorial : ℝ) - 1))) ∧
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    (∀ (m q : ℕ) (a : ℤ), 3 ≤ m → 0 < q →
      factorialGapSeries = (a : ℝ) / (q : ℝ) →
      factorialGapStepCarry m ≠ 1 →
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q) := by
  sorry
end PalomarCorpus.E68.PaperStatementsB
