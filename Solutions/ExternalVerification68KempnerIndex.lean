/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.FactorialGapPlateauCore
import ErdosProblems.Erdos68.FactorialZeroPlateauCertificates

/-!
# Source transport for the Erdős #68 Kempner-index denominator exclusion

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification68KempnerIndex

open scoped BigOperators

noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

def factorialGapPrefix (n : ℕ) : ℚ :=
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

end Erdos249257.ExternalVerification68KempnerIndex
