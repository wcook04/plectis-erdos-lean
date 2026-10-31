/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.SublogDivisorCoverage
import Solutions.PalomarCorpus.E257_51.Statement

open Filter Set

namespace PalomarCorpus.E257.RationalTailRigidity
export PalomarCorpus.E257_51.Shared (erdosSupportSeries supportCoeff)

noncomputable section

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  simpa [supportCoeff, erdosSupportSeries, binaryCoeffTail,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries,
    Erdos257PeriodNoncollapse.binaryCoeffTail] using
      Erdos257PeriodNoncollapse.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
        A hAinf p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  simpa [SupportCoeffZeroWindow, CoeffZeroWindow, supportCoeff,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.SupportCoeffZeroWindow,
    Erdos257PeriodNoncollapse.CoeffZeroWindow,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.supportCoeffZeroWindow_length_le_eps_logb_add
        A hA p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue) ε hε

theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, oddDoublingOrder,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.oddDoublingOrder,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.one_div_oddOrder_le_reciprocalMass_of_support_fraction
        A hA (by
          simpa [reciprocalSupportTerm,
            Erdos257PeriodNoncollapse.reciprocalSupportTerm] using hsum)
        p c hv hvodd hpv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
        A hAinf p c (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

end

end PalomarCorpus.E257.RationalTailRigidity
