/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.2.1: initial implications (part 1 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Classical
open Module
open Matrix
open Filter
open Topology
open ArithmeticFunction
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

namespace PalomarCorpus.E249_07.Shared
/-- The closed-form cylinder mass at the coprime node `(a,b)`: `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. Local copy of GcdMomentCalculus.cylinderMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
end PalomarCorpus.E249_07.Shared

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- The real number whose binary digits, read from position `n` on, are `d n, d (n+1), d (n+2), …`. For `n = 0` this is the number itself; for general `n` it is the tail left after `n` binary shifts. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8 := by
  sorry
/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAL

namespace PalomarCorpus.E249.PaperStructuresP
open Module
open Matrix
/-- A square nonzero evaluation minor. This is the exact finite object needed to turn number-theoretic row construction into linear independence. Local copy of Erdos249257.SeparatedMinorCertificate, restated so the compared statements elaborate against Mathlib alone. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
/-- States catalogue:cert:d3 from the long record for Erdős problem #249. Transported from Erdos249257.linearIndependent_of_separatedMinorCertificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := by
  sorry
end PalomarCorpus.E249.PaperStructuresP

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from Erdos249257.positive_rational_difference_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positive_rational_difference_lower_bound
    {whole pfx : ℚ} (hpositive : pfx < whole) :
    (1 : ℝ) /
        (((whole.den * pfx.den : ℕ) : ℝ)) ≤
      (whole : ℝ) - (pfx : ℝ) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den) := by
  sorry
/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
/-- States catalogue:mob:a1a from the long record for Erdős problem #249. Transported from Erdos249257.totient_series_eq_half_add_moebius_mersenne_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_eq_half_add_moebius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAP
open ArithmeticFunction
/-- States catalogue:mob:a1a from the long record for Erdős problem #249. Transported from MersenneLambertLadder.tsum_moebius_lambert_sq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAP

namespace PalomarCorpus.E249.PaperStatementsH
open scoped BigOperators
/-- States catalogue:mob:a1b from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsH

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisibility_mass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1) := by
  sorry
/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.pair_divisibility_mass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
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
/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_geometric_multiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAK
export PalomarCorpus.E249_07.Shared (cylinderMass)
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.cylinderMass_children_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b := by
  sorry
/-- States catalogue:mob:a8 from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
export PalomarCorpus.E249_07.Shared (cylinderMass)
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

namespace PalomarCorpus.E249.PaperStatementsB
export PalomarCorpus.E249_07.Shared (cylinderMass)
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
export PalomarCorpus.E249_07.Shared (mobiusNumeratorPolynomial spacedRepunit)
/-- The natural coefficient in the gcd-word presentation. Local copy of Erdos249257.RepunitMobiusNumerator.gcdWordCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient
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
export PalomarCorpus.E249_07.Shared (mobiusNumeratorPolynomial spacedRepunit)
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
