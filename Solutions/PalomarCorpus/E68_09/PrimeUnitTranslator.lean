/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PrimeUnitTranslator
import Solutions.PalomarCorpus.E68_09.Statement

namespace PalomarCorpus.E68.PrimeUnitTranslator

/-- The prime-pair translator has zero factorial moment. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  simpa [factorialMoment, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.factorialMoment, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using Erdos68.primeTranslator_moment_zero hp

/-- Every channel strictly below `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_lt_p hp hd2 hdp

/-- At the prime itself the sole surviving channel numerator is exactly its
normalizing modulus `p! - 1`. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_at_prime hp

/-- Every channel strictly beyond `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_p_lt hp hpd

/-- The prime-pair translator is an exact unit direction for the full
infinite channel residual. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channelResidual_eq_one hD hp hDp

/-- Appending a scaled prime translator shifts the full residual by that
integer and changes nothing else in the original support. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.appendPrimeTranslatorCoeff,
    Erdos68.appendPrimeTranslatorIndex, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.channelResidual_appendPrimeTranslator coeff index z hD hp hDp

/-- For every cutoff and support threshold, a factorial-grid block and a
prime translator pair can be chosen entirely above the threshold, with the
stated zero-channel, nonzero-moment, and residual bounds. -/
theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by
  simpa [factorialMoment, channelNumerator, primeTranslatorCoeff,
    primeTranslatorIndex, channelResidual, channelResidualTerm,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    augmentedChannelMomentMatrix, cramerChannelKernelCoeff,
    factorialGridScale, factorialGridIndex,
    Erdos68.factorialMoment, Erdos68.channelNumerator,
    Erdos68.primeTranslatorCoeff, Erdos68.primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.appendPrimeTranslatorCoeff, Erdos68.appendPrimeTranslatorIndex,
    Erdos68.augmentedChannelMomentMatrix, Erdos68.cramerChannelKernelCoeff,
    Erdos68.factorialGridScale, Erdos68.factorialGridIndex] using
    Erdos68.exists_remote_factorialGrid_primeTranslator_reduction n B

end PalomarCorpus.E68.PrimeUnitTranslator
