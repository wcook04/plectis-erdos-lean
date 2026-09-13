/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.FactorialGapPlateauCore
import ErdosProblems.Erdos68.FactorialZeroPlateauCertificates
import Solutions.PalomarCorpus.E68.Statement

open scoped BigOperators

namespace PalomarCorpus.E68.KempnerIndex
export PalomarCorpus.E68.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapStepCarry strictFacTop)

theorem rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hmiss : factorialGapStepCarry m ≠ 1)
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ (m - 1).factorial) := by
  simpa [factorialGapSeries, factorialGapPrefix, strictFacTop,
    factorialGapPredecessorGap, factorialGapStepCarry,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.factorialGapPrefix, ErdosProblems.Erdos68.strictFacTop,
    ErdosProblems.Erdos68.factorialGapPredecessorGap,
    ErdosProblems.Erdos68.factorialGapStepCarry] using
    ErdosProblems.Erdos68.rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
      hm hmiss hq hseries

theorem rational_denominator_not_dvd_fiftynine_factorial
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ Nat.factorial 59) := by
  simpa [factorialGapSeries, factorialGapPrefix, strictFacTop,
    factorialGapPredecessorGap, factorialGapStepCarry,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.factorialGapPrefix, ErdosProblems.Erdos68.strictFacTop,
    ErdosProblems.Erdos68.factorialGapPredecessorGap,
    ErdosProblems.Erdos68.factorialGapStepCarry] using
    ErdosProblems.Erdos68.rational_denominator_not_dvd_fiftynine_factorial
      hq hseries

end PalomarCorpus.E68.KempnerIndex
