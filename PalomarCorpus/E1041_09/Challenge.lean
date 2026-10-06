/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, the solved families and tetranomial spokes families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Polynomial
open scoped ComplexConjugate

namespace PalomarCorpus.E1041.SolvedFamilies
open Polynomial
/-- For complex r, s, v of modulus strictly below 1, at least one of three statements holds, the first being that for every real t in [0, 1] the product (t * r - r) * (t * r - s) * (t * r - v) has modulus at most 1. That product is the value at the point t * r of the monic cubic with roots r, s, v, so one of the three roots has its complete straight spoke from the origin inside the closed unit sublevel set of that cubic. The conclusion is the closed bound at most 1, and it names one spoke rather than a pair of roots; the fibre pullback that turns one safe spoke into a root-to-root path is ordinary mathematics. -/
theorem cubic_safeRootSpoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := by
  sorry
/-- Finite real selector for the sparse quintic z ^ 5 + a z ^ 4 + b z + c: given a real r with 0 < r < 2 and five pairs (x k, s k) with 0 ≤ s k ≤ 1 and x k ^ 2 ≤ s k satisfying the three rotated Newton moment equations, the sum of the x k equal to -r, the sum of 2 x k ^ 2 - s k equal to r ^ 2, and the sum of 4 x k ^ 3 - 3 s k x k equal to -r ^ 3, at least one of the ten unordered index pairs has both tail energies s ^ 4 * (s + r ^ 2 + 2 r x) strictly below 1. In the intended reading x k and s k are the real part and squared modulus of a rotated root and the tail energy is ‖b w k + c‖ ^ 2; that identification is ordinary mathematics, and distinct indices need not denote distinct root values. -/
theorem primitiveQuintic_twoStrictTailEnergies
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by
  sorry
namespace SharpCollinear
/-- The real number cos (π / (2 n)). For n ≥ 2 it is the scale that carries the two outermost zeros of the degree-n Chebyshev polynomial to -1 and 1. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp endpoint-normalised Chebyshev height C n = 1 / (2 ^ (n - 1) cos ^ n (π / (2 n))), written as the absolute value of (2 ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n. For n ≥ 2 it is the maximum modulus on [-1, 1] of the monic polynomial T n (cos (π / (2 n)) x) / (2 ^ (n - 1) cos ^ n (π / (2 n))), whose extreme zeros are -1 and 1. The exponent n - 1 is natural subtraction, and the absolute value is cosmetic because the expression is positive for every n ≥ 2; at n = 1 the inverse of cos (π / 2) is 0 by the Lean convention and the value is 0. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
/-- Alternation kernel of the sharp collinear theorem: if p is a real monic polynomial of degree m + 2 with p (-1) = 0 and p 1 = 0, and c is a strictly increasing family of m + 1 nodes with -1 < c 0, c (Fin.last m) < 1 and |c i| ≤ 1 for every i, whose values alternate in sign in the sense that p (c i) * p (c (i+1)) < 0 for every consecutive pair, then some node satisfies |p (c i)| ≤ comparisonBound (m + 2). The affine normalisation of a complex collinear root set to this configuration, the choice of gap maxima and the transport back to the original line are ordinary mathematics outside this declaration. -/
theorem existsPeakLeComparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  sorry
end SharpCollinear
end PalomarCorpus.E1041.SolvedFamilies

namespace PalomarCorpus.E1041.TetranomialSpokes
open scoped ComplexConjugate
/-- Exact Abel identity at a root of a centred tetranomial: if w satisfies w ^ m + a * w ^ r + b * w ^ s + c = 0 then for every real u the value of z ↦ z ^ m + a z ^ r + b z ^ s + c at the point u * w equals (1 - u ^ s) * c - (u ^ s - u ^ r) * (a * w ^ r + w ^ m) - (u ^ r - u ^ m) * w ^ m, with the real coefficients cast into the complex numbers. No ordering of the natural exponents and no bound on u is assumed. -/
theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry
/-- Root-dependent budget: for 1 ≤ s ≤ r ≤ m, a root w of z ^ m + a z ^ r + b z ^ s + c with ‖w‖ < 1 and ‖c‖ < 1 satisfying ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1, and every real u in [0, 1], the tetranomial has modulus strictly below 1 at u * w. The complete spoke from the origin to that root therefore lies in the open unit lemniscate, with the coefficient a unrestricted. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry
/-- Coefficient-only corollary of the same conclusion, with the root-dependent budget replaced by ‖b‖ + ‖c‖ ≤ 1 under the same hypotheses 1 ≤ s ≤ r ≤ m, w a root of z ^ m + a z ^ r + b z ^ s + c, ‖w‖ < 1, ‖c‖ < 1 and u in [0, 1]: the complete spoke of every such root lies in the open unit lemniscate, again with a unrestricted. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry
/-- Exact energy identity for a finite family: for a Finset S, a family v of complex numbers indexed by its type, and complex b and c, the sum over i in S of Complex.normSq (c + b * v i) equals the cardinality of S, cast to a real, times Complex.normSq c, plus Complex.normSq b times the sum of Complex.normSq (v i), plus twice the real part of conj c * b * (the sum of the v i). The signed mixed-moment term is what lets this identity certify configurations outside the coefficient-only region ‖b‖ + ‖c‖ ≤ 1. -/
theorem sum_normSq_const_add_mul
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) :
    ∑ i ∈ S, Complex.normSq (c + b * v i) =
      (S.card : ℝ) * Complex.normSq c +
        Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
          2 * (conj c * b * (∑ i ∈ S, v i)).re := by
  sorry
/-- Pigeonhole consequence of that identity: if S has at least two elements and the energy on the right of the identity is strictly less than the cardinality of S, cast to a real, minus 1, then there are two distinct indices i and j in S with ‖c + b * v i‖ < 1 and ‖c + b * v j‖ < 1. Supporting selector for the indexed-root form below. -/
theorem exists_two_tails_norm_lt_one_of_exact_L2_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (hcard : 2 ≤ S.card)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  sorry
/-- Indexed-root form: for a Finset S with at least two elements, a family w with every w i, i in S, a root of z ^ m + a z ^ r + b z ^ s + c of modulus below 1, exponents 1 ≤ s ≤ r ≤ m, ‖c‖ < 1, signed moment equal to the sum of the w i ^ s over S, and coefficient budget card S * (Complex.normSq b + Complex.normSq c) + 2 * (conj c * b * moment).re < card S - 1, there are two distinct indices i and j in S whose complete spokes u ↦ u * w i and u ↦ u * w j, for u in [0, 1], keep the tetranomial strictly below modulus 1. The two indices are distinct; distinct root values require in addition that w be injective on S. -/
theorem exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget
    {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c moment : ℂ}
    (hcard : 2 ≤ S.card)
    (hroot : ∀ i ∈ S, w i ^ m + a * w i ^ r + b * w i ^ s + c = 0)
    (hw : ∀ i ∈ S, ‖w i‖ < 1) (hc : ‖c‖ < 1)
    (hmoment : ∑ i ∈ S, w i ^ s = moment)
    (hcoeff :
      (S.card : ℝ) * (Complex.normSq b + Complex.normSq c) +
          2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r +
          b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r +
          b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) := by
  sorry
end PalomarCorpus.E1041.TetranomialSpokes
