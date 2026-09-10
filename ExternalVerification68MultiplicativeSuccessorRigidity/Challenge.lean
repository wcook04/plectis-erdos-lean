/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 multiplicative successor rigidity

On the rational branch the strict successor is purely multiplicative, every
fixed modulus eventually divides it, and a cofinal failure of one fixed
congruence proves irrationality.  No theorem here produces such a cofinal
failure, so the package does not solve Erdős Problem 68.
-/

namespace Erdos249257.ExternalVerification68MultiplicativeSuccessorRigidity

open scoped BigOperators

noncomputable section

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
  sorry

theorem gapSuccessor_dvd_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m → gapSuccessor j ∣ gapSuccessor m := by
  sorry

theorem factorial_mul_gapSuccessor_eq_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m →
      (j.factorial : ℤ) * gapSuccessor m = (m.factorial : ℤ) * gapSuccessor j := by
  sorry

theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  sorry

theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry

theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry

theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m := by
  sorry

end

end Erdos249257.ExternalVerification68MultiplicativeSuccessorRigidity
