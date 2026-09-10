/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.MultiplicativeSuccessorRigidity

/-!
# Source transport for the Erdős #68 multiplicative successor rigidity

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification68MultiplicativeSuccessorRigidity

open scoped BigOperators

noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m

theorem gapSuccessor_eq_mul_pred_of_dvd
    {m : ℕ} (hm : 3 ≤ m) (h : (m : ℤ) ∣ gapSuccessor m) :
    gapSuccessor m = (m : ℤ) * gapSuccessor (m - 1) := by
  simpa [gapSuccessor, strictFacTopRat, factorialGapPrefix,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.gapSuccessor_eq_mul_pred_of_dvd hm h

theorem gapSuccessor_dvd_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m → gapSuccessor j ∣ gapSuccessor m := by
  simpa [gapSuccessor, strictFacTopRat, factorialGapPrefix,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.gapSuccessor_dvd_of_eventually_dvd hM h hj

theorem factorial_mul_gapSuccessor_eq_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m →
      (j.factorial : ℤ) * gapSuccessor m = (m.factorial : ℤ) * gapSuccessor j := by
  simpa [gapSuccessor, strictFacTopRat, factorialGapPrefix,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.factorial_mul_gapSuccessor_eq_of_eventually_dvd hM h hj

theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  simpa [factorialGapSeries, gapSuccessor, strictFacTopRat, factorialGapPrefix,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.eventually_dvd_gapSuccessor_of_not_irrational hd hrat

theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  simpa [factorialGapSeries, gapSuccessor, strictFacTopRat, factorialGapPrefix,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
      hd h

theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  simpa [factorialGapSeries, gapSuccessor, strictFacTopRat, factorialGapPrefix,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor h

theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m := by
  simpa [factorialGapSeries, gapSuccessor, strictFacTopRat, factorialGapPrefix,
    Erdos68.factorialGapSeries, Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
    ErdosProblems.Erdos68.gapSuccessor, ErdosProblems.Erdos68.strictFacTopRat,
    ErdosProblems.Erdos68.factorialGapPrefix] using
    ErdosProblems.Erdos68.not_eventually_odd_gapSuccessor_of_not_irrational hrat

end Erdos249257.ExternalVerification68MultiplicativeSuccessorRigidity
