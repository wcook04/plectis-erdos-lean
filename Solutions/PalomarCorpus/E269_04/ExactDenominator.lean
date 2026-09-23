/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos269.PaperExactDenominatorR13
import Mathlib
import Solutions.PalomarCorpus.E269_04.Statement

open scoped BigOperators

namespace PalomarCorpus.E269.ExactDenominator
export PalomarCorpus.E269_04.Shared (dyadicShellMassQ235 dyadicSmoothShell235 dyadicSmoothWindowMassQ235 heightNormalizer235 rationalTailState smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)

theorem exact_denominators_and_threshold_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N
          (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N
          (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a) := by
  have hval' : ErdosProblems.Erdos269.PaperR7.paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ) := by
    rw [ErdosProblems.Erdos269.PaperR7.paperSeries235_eq_shellTsum]
    simpa [paperSeries235, dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      dyadicShellMassR235, dyadicShellMassQ235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using hval
  have h := ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing
    hB hB30 hcop ha hval'
  have hthreshold :
      (ErdosProblems.Erdos269.PaperR13.firstClearingIndex u v w ≤ a ↔
        2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a) := by
    rw [← ErdosProblems.Erdos269.PaperR13.clearingCondition_iff_firstClearingIndex_le]
    simp [ErdosProblems.Erdos269.PaperR13.ClearingCondition, ha]
  simpa [rationalTailState, heightNormalizer235, dyadicSmoothWindowMassQ235,
    ErdosProblems.Erdos269.PaperR13.rationalTailState,
    ErdosProblems.Erdos269.heightNormalizer235,
    ErdosProblems.Erdos269.dyadicSmoothWindowMassQ235,
    dyadicShellMassQ235, dyadicSmoothShell235, strictSmoothShell,
    strictSmoothExponents, threePrimeHeight, smooth3Val,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.smooth3Val, hthreshold] using h

end PalomarCorpus.E269.ExactDenominator
