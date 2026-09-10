/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.RationalLatticeReduction
import Solutions.PalomarCorpus.E269.Shared

open scoped BigOperators

namespace PalomarCorpus.E269.AllScaleLattice
export PalomarCorpus.E269.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)

noncomputable abbrev heightNormalizer235 := ErdosProblems.Erdos269.heightNormalizer235
noncomputable abbrev dyadicSmoothWindowMassQ235 :=
  ErdosProblems.Erdos269.dyadicSmoothWindowMassQ235

theorem smoothHeight_mul_prime_dvd_boundaryHeight
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) :=
  ErdosProblems.Erdos269.smoothHeight_mul_prime_dvd_boundaryHeight hp hx hlt

theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) :
    2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) :=
  ErdosProblems.Erdos269.two_mul_heightNormalizer235 a ha

theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) :=
  ErdosProblems.Erdos269.heightNormalizer235_mul_windowMass_eq_int start count

theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) :
    dyadicShellTsumTailR235 a =
      ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) +
        dyadicShellTsumTailR235 (a + k) :=
  ErdosProblems.Erdos269.dyadicShellTsumTailR235_eq_range_add a k

theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a =
        (k : ℝ) :=
  ErdosProblems.Erdos269.qsmul_normalizedTailState_eq_int_of_value_eq_rat
    hq hval ha

theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) =
          (z : ℝ) :=
  ErdosProblems.Erdos269.exists_normalizedTailState_collision_of_value_eq_rat
    hq hval

end PalomarCorpus.E269.AllScaleLattice
