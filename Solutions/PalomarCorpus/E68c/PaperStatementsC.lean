/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.FactorialChannelCertificate
import ErdosProblems.Erdos68.FactorialShiftFamilyOrbit
import ErdosProblems.Erdos68.PaperCompleteExisting
import ErdosProblems.Erdos68.PaperCompleteSupportedBands
import ErdosProblems.Erdos68.PrimeUnitTranslator
import Solutions.PalomarCorpus.E68c.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.PaperStatementsC

theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n := @ErdosProblems.Erdos68.PaperComplete.supported_breakpoint_escape f d hlo hz hm

theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0 := @ErdosProblems.Erdos68.PaperComplete.supported_first_band_cancellation f d hlo hhi hz

theorem supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := @ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form f d hd

theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d := @ErdosProblems.Erdos68.PaperComplete.supported_quotient_band f d k hlo hhi

theorem uniform_family_boundary {t : ℤ} (ht : -1 ≤ t) :
    (¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) ∧
    (Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) := @ErdosProblems.Erdos68.PaperComplete.uniform_family_boundary t ht

theorem uniform_family_members :
    shiftGapSeries (-1) = factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1) := @ErdosProblems.Erdos68.PaperComplete.uniform_family_members

end PalomarCorpus.E68.PaperStatementsC
