/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269_04

Every non-theorem declaration of `PalomarCorpus/E269_04/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E269_04.Shared
/-- The integer-power condition defining the paper's first clearing index. Local copy of ErdosProblems.Erdos269.PaperR13.ClearingCondition, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The finite set of exponent triples `(i, j, k)`, each entry smaller than `x`, whose smooth value `p ^ i * q ^ j * r ^ k` is strictly less than `x`; for generators at least 2 the entrywise cap is never binding, so the set is exactly the triples whose smooth value is below `x`, and for pairwise distinct primes those values are exactly the `{p, q, r}`-smooth numbers below `x`. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- The exponent triples counted by `strictSmoothExponents` at `y` and not at `x`; for generators at least 2 and `x ≤ y` these are exactly the triples whose smooth value lies in the half open interval from `x` to `y`. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The `a`th dyadic shell for the primes 2, 3 and 5: the exponent triples `(i, j, k)` with `2 ^ a ≤ 2 ^ i * 3 ^ j * 5 ^ k < 2 ^ (a + 1)`. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The rational mass of the `a`th dyadic shell, the sum over that shell of the reciprocal of the three-prime height of the corresponding smooth value. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- The rational mass of the count consecutive dyadic smooth shells starting at start, with an empty window having mass zero. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
/-- The natural number H(2^a)/2, where H is the three-prime running height for 2, 3 and 5; the denominator theorem uses positive scales. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The rational normalized tail obtained from a proposed value N/D by subtracting the initial term 1 and the shells at scales 1 through a-1, then multiplying by H(2^a)/2. -/
noncomputable def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))
end PalomarCorpus.E269_04.Shared

namespace PalomarCorpus.E269.ExactDenominator
open scoped BigOperators
export PalomarCorpus.E269_04.Shared (dyadicShellMassQ235 dyadicSmoothShell235 dyadicSmoothWindowMassQ235 heightNormalizer235 rationalTailState smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The normalized state at scale `a` of an arbitrary real tail function `tail`, namely `(H (2 ^ a) / 2) * tail a` with the three-prime height for 2, 3 and 5 cast to the reals and the division taken in the reals. -/
noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The real cast of the rational shell mass `dyadicShellMassQ235`. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The tail of the shell masses from scale `a` onward, taken as the Mathlib unconditional sum of `dyadicShellMassR235 (a + n)` over `n`; summability is proved in `actual_dyadicShellOrbit_recurrence_and_escape`, so this is the genuine infinite sum, and the value at `a = 0` is the reciprocal running least common multiple sum of Erdős problem 269 for the prime set `{2, 3, 5}`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The genuine normalized state `(H (2 ^ a) / 2) * T a` of the literal `{2,3,5}` shell tail, that is `dyadicNormalizedTailStateR235` applied to the actual tail `dyadicShellTsumTailR235`. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
/-- The sum of the real dyadic shell masses from scale zero, equal to the literal reciprocal running-LCM series at the primes 2, 3 and 5. -/
noncomputable def paperSeries235 : ℝ := dyadicShellTsumTailR235 0
end PalomarCorpus.E269.ExactDenominator

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
export PalomarCorpus.E269_04.Shared (ClearingCondition)
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.PaperStatementsF
open scoped BigOperators
export PalomarCorpus.E269_04.Shared (ClearingCondition dyadicShellMassQ235 dyadicSmoothShell235 dyadicSmoothWindowMassQ235 heightNormalizer235 rationalTailState smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The paper's elementary bound `a_D = u+1+2v+3w` satisfies all three integer-power thresholds. Local copy of ErdosProblems.Erdos269.PaperR13.clearingCondition_sufficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearingCondition_sufficient (u v w : ℕ) :
    ClearingCondition u v w (u + 1 + 2 * v + 3 * w) := by
  let aD := u + 1 + 2 * v + 3 * w
  have h2 : 2 ^ (u + 1) ≤ 2 ^ aD :=
    Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega)
  have h3four : 3 ^ v ≤ 4 ^ v := Nat.pow_le_pow_left (by norm_num) v
  have h4two : 4 ^ v = 2 ^ (2 * v) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : 3 ^ v ≤ 2 ^ aD := by
    rw [h4two] at h3four
    exact h3four.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  have h5eight : 5 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
  have h8two : 8 ^ w = 2 ^ (3 * w) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h5 : 5 ^ w ≤ 2 ^ aD := by
    rw [h8two] at h5eight
    exact h5eight.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  exact ⟨by omega, h2, h3, h5⟩
/-- The first positive scale satisfying the three integer-power comparisons. Local copy of ErdosProblems.Erdos269.PaperR13.firstClearingIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def firstClearingIndex (u v w : ℕ) : ℕ := by
  classical
  exact Nat.find ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩
end PalomarCorpus.E269.PaperStatementsF
