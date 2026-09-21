/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperFixedStartResidueR14
import Solutions.PalomarCorpus.E269.Statement

open Filter
open scoped Topology BigOperators

namespace PalomarCorpus.E269.FixedStartResidue
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 leastPositiveResidue smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState windowForcing)

theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_formula B lo hB

theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo)) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.fixedStartResidue_ratio_tendsto B lo hB

theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_eq_tail_of_integral B lo hB hInt

end PalomarCorpus.E269.FixedStartResidue
