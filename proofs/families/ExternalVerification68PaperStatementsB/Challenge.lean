/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #68

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos68.ChannelBreakpointRigidity`,
`ErdosProblems.Erdos68.ChannelIntegralCongruence`,
`ErdosProblems.Erdos68.FactorialGapPlateauCore`,
`ErdosProblems.Erdos68.PaperCompleteExisting`, `ErdosProblems.Erdos68.PrimeUnitTranslator`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification68PaperStatementsB

noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1

noncomputable def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ :=
  ![(p : ℤ), -1]

noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ :=
  ![p - 1, p]

noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

/-- States long68:res:translator from the long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.prime_channel_corrector in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    factorialMoment (primeTranslatorCoeff p)
      (primeTranslatorIndex p) = 0 ∧
    channelNumerator (primeTranslatorCoeff p)
      (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      channelNumerator (primeTranslatorCoeff p)
        (primeTranslatorIndex p) d = 0) := by
  sorry

/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported
from ErdosProblems.Erdos68.PaperComplete.radius_no_eventual_ratio_upper in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := by
  sorry

/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported
from ErdosProblems.Erdos68.PaperComplete.radius_not_littleO in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := by
  sorry

/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported
from ErdosProblems.Erdos68.PaperComplete.square_subsequence_radius in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  sorry

/-- States long68:eq:carry-rationality, long68:eq:strict-misses, long68:eq:unit-window from the
long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.strict_successor_characterisation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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

end Erdos249257.ExternalVerification68PaperStatementsB
