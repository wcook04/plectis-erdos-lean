/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DyadicShellSummability
import Solutions.PalomarCorpus.E269.Shared

open scoped BigOperators

namespace PalomarCorpus.E269.ActualShellOrbit
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)

noncomputable section

noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

theorem actual_dyadicShellOrbit_recurrence_and_escape :
    Summable dyadicShellMassR235 ∧
      (∀ a : ℕ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
          dyadicBlockBase235 a *
              dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
            dyadicOrderedBlockDigit235 a) ∧
      ((∃ a : ℕ, ∃ z : ℤ,
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
        ∀ a₀, ∃ a, a₀ ≤ a ∧
          FarFromIntegers
            (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
            ((1 : ℝ) / 31)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [dyadicShellMassR235, dyadicShellMassQ235,
      dyadicSmoothShell235, strictSmoothShell, strictSmoothExponents,
      threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.summable_dyadicShellMassR235
  · intro a
    simpa [dyadicNormalizedTailStateR235, dyadicShellTsumTailR235,
      dyadicShellMassR235, dyadicShellMassQ235, dyadicBlockBase235,
      DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicNormalizedShellTsumTailR235_succ a
  · simpa [FarFromIntegers, dyadicNormalizedTailStateR235,
      dyadicShellTsumTailR235, dyadicShellMassR235, dyadicShellMassQ235,
      dyadicBlockBase235, DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.FarFromIntegers,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicShellTsumTail_integer_or_cofinal_far

end

end PalomarCorpus.E269.ActualShellOrbit
