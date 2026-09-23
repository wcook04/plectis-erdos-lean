/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.ChannelBreakpointRigidity
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.FactorialGapPlateauCore
import ErdosProblems.Erdos68.PaperCompleteExisting
import ErdosProblems.Erdos68.PrimeUnitTranslator
import Solutions.PalomarCorpus.E68_04.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.PaperStatementsB

noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1

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

theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    factorialMoment (primeTranslatorCoeff p)
      (primeTranslatorIndex p) = 0 ∧
    channelNumerator (primeTranslatorCoeff p)
      (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      channelNumerator (primeTranslatorCoeff p)
        (primeTranslatorIndex p) d = 0) := @ErdosProblems.Erdos68.PaperComplete.prime_channel_corrector p hp

theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := @ErdosProblems.Erdos68.PaperComplete.radius_no_eventual_ratio_upper M R hH

theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := @ErdosProblems.Erdos68.PaperComplete.radius_not_littleO M R hH

theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := @ErdosProblems.Erdos68.PaperComplete.square_subsequence_radius t M R ht hM hdiv hsmall

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
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q) := @ErdosProblems.Erdos68.PaperComplete.strict_successor_characterisation

end PalomarCorpus.E68.PaperStatementsB
