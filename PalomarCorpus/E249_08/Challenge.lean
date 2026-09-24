/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.2.1: initial implications (part 2 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
open scoped Pointwise
open ArithmeticFunction

namespace PalomarCorpus.E249_08.Shared
/-- The closed-form cylinder mass at the coprime node `(a,b)`: `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. Local copy of GcdMomentCalculus.cylinderMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
/-- The second Jordan totient, as the integer-valued Dirichlet convolution `μ * id²`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)
/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lambertValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
end PalomarCorpus.E249_08.Shared

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_08.Shared (lambertValue)
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisibility_mass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_coefficient_moments in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_mobiusTermKernel_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0 := by
  sorry
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_eq_divisor_sum_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_affine_in_multiplier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusTermKernel_affine_in_multiplier (d H m : ℕ) :
    mobiusTermKernel d (m * H)
      = (m : ℝ) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_moment_annihilation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0 := by
  sorry
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.stopping_probability_ge_third in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem stopping_probability_ge_third (a b : ℕ+) :
    (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
      / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := by
  sorry
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.stopping_transition_probabilities_sum_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem stopping_transition_probabilities_sum_one (a b : ℕ+) :
    ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
        / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
export PalomarCorpus.E249_08.Shared (cylinderMass)
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cylinderMass_eq_divisibility_mass_mul in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cylinderMass_eq_divisibility_mass_mul (a b : ℕ+) :
    cylinderMass a b
      = (∑' k : ℕ, if 0 < k ∧ (a : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
        * (∑' k : ℕ, if 0 < k ∧ (b : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0) := by
  sorry
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cylinder_mediant_split in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cylinder_mediant_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) := by
  sorry
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cylinder_root_values in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cylinder_root_values :
    cylinderMass 1 1 = 1 ∧
      1 / ((2 : ℝ) ^ (((1 : ℕ+) : ℕ) + ((1 : ℕ+) : ℕ)) - 1) = 1 / 3 ∧
      cylinderMass (1 + 1) 1 = 1 / 3 ∧ cylinderMass 1 (1 + 1) = 1 / 3 := by
  sorry
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.normalised_split_probabilities in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem normalised_split_probabilities (a b : ℕ+) :
    (1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)) / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
          / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass (a + b) b / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass a (a + b) / cylinderMass a b
        = ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsAK
export PalomarCorpus.E249_08.Shared (cylinderMass)
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.cylinderMass_children_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsB
export PalomarCorpus.E249_08.Shared (cylinderMass)
/-- The depth-`d` finite unfolding of the mediant recursion: sum the stop mass `1/(2^{a+b}-1)` at every node of the first `d` generations of the subtree rooted at `(a,b)`, under the children `(a+b, b)` and `(a, a+b)`. Local copy of GcdMomentCalculus.sternBrocotDepthMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sternBrocotDepthMass : ℕ → ℕ+ → ℕ+ → ℝ
  | 0, _, _ => 0
  | (dp + 1), a, b =>
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + sternBrocotDepthMass dp (a + b) b + sternBrocotDepthMass dp a (a + b)
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.sternBrocotDepthMass_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sternBrocotDepthMass_error (dp : ℕ) :
    ∀ a b : ℕ+,
      0 ≤ cylinderMass a b - sternBrocotDepthMass dp a b
        ∧ cylinderMass a b - sternBrocotDepthMass dp a b
            ≤ (2 / 3 : ℝ) ^ dp * cylinderMass a b := by
  sorry
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tendsto_sternBrocotDepthMass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_sternBrocotDepthMass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (cylinderMass a b)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsB

namespace PalomarCorpus.E249.PaperStatementsAC
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)
/-- The natural coefficient in the gcd-word presentation. Local copy of Erdos249257.RepunitMobiusNumerator.gcdWordCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.cyclotomic_dvd_mobiusNumeratorPolynomial_sub in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by
  sorry
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo_eq_prod_primeFactors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1) := by
  sorry
/-- States catalogue:mob:b1 from the long record for Erdős problem #249. Transported from Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumeratorPolynomial_coeff {r k : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).coeff k =
      if k < r then (gcdWordCoeff r k : ℤ) else 0 := by
  sorry
/-- States catalogue:mob:b1 from the long record for Erdős problem #249. Transported from Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumeratorPolynomial_coeff_pos {r k : ℕ}
    (hr : Squarefree r) (hk : k < r) :
    0 < (mobiusNumeratorPolynomial r).coeff k := by
  sorry
end PalomarCorpus.E249.PaperStatementsAC

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)
/-- Integer evaluation `Φ_m(2)`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. Local copy of Erdos249257.RadicalMobiusShadow.baseMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_mod_cyclotomicEval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by
  sorry
/-- States catalogue:mob:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.numerator_eval_two_divisors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem numerator_eval_two_divisors {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      ∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((mersenne r /
            mersenne d : ℕ) : ℤ)) := by
  sorry
/-- States catalogue:mob:b3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.radical_decomposition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radical_decomposition (H r : ℕ) (hH : 0 < H) (hr : 0 < r) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) * baseMobiusShadow (squarefreeKernel H) ∧
    (baseMobiusShadow r).den = mersenne r /
      ((mobiusNumeratorPolynomial r).eval 2).natAbs.gcd (mersenne r) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAQ

namespace PalomarCorpus.E249.PaperStatementsAS
open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open scoped Pointwise
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (mobiusNumeratorPolynomial spacedRepunit)
/-- States catalogue:mob:b8a from the long record for Erdős problem #249. Transported from Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_new_fibre in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  sorry
/-- States catalogue:mob:b8b from the long record for Erdős problem #249. Transported from Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_old_fibre in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r := by
  sorry
end PalomarCorpus.E249.PaperStatementsAS

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_08.Shared (lambertValue)
/-- The Euler totient as an integer-valued arithmetic function. Local copy of MersenneLambertLadder.totientZ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩
/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution). `A(n)` counts the primitive Dirichlet characters of conductor `n` (OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on `n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. Local copy of MersenneLambertLadder.primWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ) := by
  sorry
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry
end PalomarCorpus.E249.PaperStatementsBA
