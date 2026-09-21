/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041

The degree-seven counterexample below formalises one instance of ani’s construction. Its roots are distinct and lie in the open
unit disc, while every continuous path in the strict unit lemniscate between distinct roots has total variation greater than 2.
The declaration concerns this precise total-variation formulation; it does not formalise the small-parameter family or a
Hausdorff-measure comparison. Historical correspondence has not received independent human review.

`DegreeSevenCounterexample`: the exact existential polynomial and universal path obstruction. The remaining families record
positive results under their own hypotheses; the counterexample does not change those statements.

`CubicPath`: the complete degree-three case. For a monic cubic with all zeros in the open unit disc, two zeros are joined by an
explicit two-segment path that is continuous, of bounded variation on `[0, 2]`, contained in `{|p| < 1}`, and of extended
variation strictly below 2. Squarefreeness makes the selected zeros distinct. Pendyala (arXiv:2606.24875) proves degree four;
priority for degree three is not adjudicated here. For translated cubic quotient fibres the same two-segment path, taken through
the centre `h`, joins two distinct zeros of `z ↦ P ((z - h) ^ q)` inside `{|P ((z - h) ^ q)| < 1}` with extended variation below
2, for every monic cubic `P` and every `q ≥ 2` such that all zeros of that function lie in the open unit disc and two of them are
distinct.

`SolvedFamilies`: the alternation kernel of the sharp collinear theorem, whose constant `C_n = 1 / (2^(n-1) cos^n(pi / (2n)))` is
attained, as the companion paper records and no compared declaration states, by the endpoint normalised Chebyshev configuration;
the finite two-tail selector for the sparse quintic `z^5 + a z^4 + b z + c`; and the safe origin spoke for three open-disc cubic
roots. Affine normalisation, moment identification and path assembly are ordinary mathematics outside these statements.

`CriticalGeometry`: at a critical point two root occurrences have total distance to it at most twice the geometric mean of the n
distances, with a real-scalar budget read as bounding the two smallest by 2; and two exact configurations, a quintic whose unique
nearest spoke escapes and a cubic whose every root-pair midpoint escapes, closing the straight-line routes. Curved connectors
remain.

`CriticalValueMean`: for a monic polynomial `p` of degree `n ≥ 2` with all zeros in a closed disc of radius `R ≥ 0`, the critical
values satisfy `∑ ‖p c‖ ^ (2 / (n - 1)) ≤ (n - 1) R ^ (2 n / (n - 1))` and `∑ ‖p c‖ ^ (1 / n) ≤ (n - 1) R`, the sums running over
the critical points with multiplicity.

`CyclicTrinomialFiber` and `TetranomialSpokes`: exact Abel factorisations at a root, with coefficient and signed-moment budgets
forcing complete radial spokes inside the unit lemniscate. Distinct indices denote distinct root values only under injectivity.

`QuarticQuotientFiber`: the root-lift density comparison, the exact axis integral, and the powered endpoint budget below 2.

`FirstMergeCriticalValueSeparation`: exact thresholds for the coefficient `C(n, S) = (1 + S)^(2/n) log(S / (S - 1))` and the
sign-free length consumer. The uniformisation, univalence, Bergman and Pólya inputs behind the analytic bound are ordinary
mathematics.
-/

open Finset
open Polynomial Set
open scoped BigOperators
open Polynomial
open scoped ComplexConjugate
open scoped ENNReal
open Polynomial Metric

namespace PalomarCorpus.E1041.CriticalGeometry
open Finset
/-- For n at least 2, complex points z 0 through z (n-1) and a point c differing from every z k, if the reciprocals (c - z k)⁻¹ sum to zero, so that c is a critical point of the monic polynomial with those root occurrences, and r is the positive real with r ^ n equal to the product of the distances ‖c - z k‖, then two distinct indices i and j satisfy ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r: some two root occurrences have total distance at most twice the geometric mean of all n root distances. The conclusion is about distances only and asserts no containment of the two segments in any sublevel set. -/
theorem criticalGeometricMean_twoRootProximity
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  sorry
/-- A real-scalar inequality in N, t, δ and e with no polynomial, root or critical point in its statement: for reals N ≥ 2, t < 1 and 0 < δ ≤ e with δ ≤ 1, e ≤ 1 + t, e ≤ (N - 1) * δ and N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2), the sum δ + e is at most 2. It is the scalar core of the unit-disc two-nearest-root budget, whose intended reading takes N as the degree, t as the modulus of the critical point, and δ ≤ e as the two smallest distances from that point to the roots; deriving those hypotheses from a polynomial is ordinary mathematics outside this declaration. -/
theorem criticalDiskInverseBalance_twoRootProximity
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e ≤ 2 := by
  sorry
/-- The same real-scalar hypotheses as criticalDiskInverseBalance_twoRootProximity with e ≤ 1 + t strengthened to e < 1 + t, which upgrades the conclusion from δ + e ≤ 2 to δ + e < 2; like that declaration it names no polynomial. -/
theorem criticalDiskInverseBalance_twoRootProximity_strict
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e < 2 := by
  sorry
/-- The rational number 999/1000 viewed as a complex number, the common modulus of four of the five roots of the explicit quintic used for the unique-nearest-spoke obstruction. -/
noncomputable def nearestSpokeP : ℂ := (999 : ℂ) / 1000
/-- The real number (901/902) * (999/1000) = 900099/902000 viewed as a complex number, the root of index 0 in nearestSpokeRoot and the one of strictly smallest modulus among the five. -/
noncomputable def nearestSpokeA : ℂ := ((901 : ℂ) / 902) * nearestSpokeP
/-- The complex number (-451 + 780 i)/901, which has modulus exactly 1 because 451 ^ 2 + 780 ^ 2 = 901 ^ 2; it places the root of index 3 in nearestSpokeRoot on the circle of radius p. -/
noncomputable def nearestSpokeUPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901
/-- The complex conjugate (-451 - 780 i)/901 of the previous unimodular factor, placing the root of index 4 in nearestSpokeRoot on the same circle of radius p. -/
noncomputable def nearestSpokeUMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901
/-- The five roots of the explicit quintic obstruction indexed by Fin 5: the real root a = 900099/902000, the conjugate pair i p and -i p with p = 999/1000, and the conjugate pair p u₊ and p u₋ of the same modulus p. -/
noncomputable def nearestSpokeRoot : Fin 5 → ℂ
  | 0 => nearestSpokeA
  | 1 => Complex.I * nearestSpokeP
  | 2 => -Complex.I * nearestSpokeP
  | 3 => nearestSpokeP * nearestSpokeUPlus
  | 4 => nearestSpokeP * nearestSpokeUMinus
/-- The reciprocals of the five listed roots sum to zero, so the origin is a critical point of the monic quintic whose roots are exactly those five points. -/
theorem nearestSpoke_reciprocal_balance :
    ∑ k, (nearestSpokeRoot k)⁻¹ = 0 := by
  sorry
/-- Every index k other than 0 satisfies Complex.normSq (root 0) < Complex.normSq (root k), so the real root a is the strictly unique nearest root to the critical point at the origin; squared moduli are used so that the exact certificate involves no square root. -/
theorem nearestSpoke_unique_nearest_normSq :
    (∀ k : Fin 5, k ≠ 0 →
      Complex.normSq (nearestSpokeRoot 0) < Complex.normSq (nearestSpokeRoot k)) := by
  sorry
/-- Exact rational inequality stating that a displayed product of four positive rationals exceeds 1. That product is the factored modulus of the monic quintic with the five listed roots at the point z = a/10: the first two factors give ‖z - a‖ = a * (1 - 1/10), the third is ‖z ^ 2 + p ^ 2‖ from the conjugate pair ± i p, and the fourth is ‖z ^ 2 + p ^ 2 / 10 + p ^ 2‖ from the pair p u₊, p u₋. The straight spoke from the critical point at the origin to the unique nearest root leaves the open unit lemniscate once that product is identified with the quintic's modulus at the spoke point, an identification no compared declaration states, which excludes the unique-nearest-root tie-breaking route. -/
theorem nearestSpoke_unique_nearest_spoke_escapes :
    (1 : ℝ) <
      (900099 / 902000 : ℝ) * (1 - 1 / 10) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
          (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by
  sorry
/-- The rational number 99/100 viewed as a complex number, the common modulus of the three roots of the explicit cubic used for the all-pairs midpoint obstruction. -/
noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100
/-- The primitive cube root of unity -1/2 + (√3 / 2) i, written with the real square root of 3 cast into the complex numbers. -/
noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I
/-- The three roots R, R ω and R ω ^ 2 of the explicit cubic obstruction, indexed by Fin 3, with R = 99/100 and ω the primitive cube root of unity. -/
noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2
/-- The monic cubic function z ↦ z ^ 3 - (99/100) ^ 3, whose zeros are exactly the three listed points. -/
noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3
/-- Each of the three listed points is a zero of that monic cubic. Supporting lemma for the midpoint obstruction. -/
theorem allStraightCubic_roots :
    ∀ k : Fin 3, allStraightCubic (allStraightRoot k) = 0 := by
  sorry
/-- Each of the three listed roots has modulus strictly less than 1, so this cubic satisfies the open-unit-disc hypothesis of the parent problem. Supporting lemma for the midpoint obstruction. -/
theorem allStraightCubic_roots_in_unitDisk :
    ∀ k : Fin 3, ‖allStraightRoot k‖ < 1 := by
  sorry
/-- For every pair of distinct indices i and j the midpoint (root i + root j) / 2 has cubic value of modulus strictly greater than 1, so for this cubic no straight segment between two roots stays inside the open unit lemniscate. The statement excludes the straight root-pair segment for this polynomial; it is no counterexample to the parent problem, which permits curved connectors. -/
theorem allStraightCubic_every_pair_midpoint_escapes :
    ∀ i j : Fin 3, i ≠ j →
      1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by
  sorry
end PalomarCorpus.E1041.CriticalGeometry

namespace PalomarCorpus.E1041.CriticalValueMean
open Polynomial
open scoped BigOperators
/-- Every zero of the complex polynomial `p` lies in the closed disc of radius `R` about `h`: `p.eval z = 0` implies `‖z - h‖ ≤ R`. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- The family `c` indexed by `Fin (n - 1)` lists the critical points of `p` with multiplicity: the derivative of `p` equals `C (n : ℂ)` times the product over `j` of `X - C (c j)`. For a monic `p` of degree `n` this says that `c` enumerates the `n - 1` zeros of the derivative, each as often as its multiplicity. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Critical-value mean in every degree. Let `n ≥ 2`, let `p` be a monic complex polynomial of degree `n` all of whose zeros lie in the closed disc of radius `R ≥ 0` about a centre `h`, and let `c` enumerate its `n - 1` critical points with multiplicity. Then the sum over `j` of `‖p (c j)‖ ^ (2 / (n - 1))` is at most `(n - 1) R ^ (2 n / (n - 1))`, and the sum over `j` of `‖p (c j)‖ ^ (1 / n)` is at most `(n - 1) R`. The exponents are real powers, the centre `h` is arbitrary, and the degenerate radius `R = 0` is included. -/
theorem paper_critical_value_mean (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ)
    (hn : 2 ≤ n) (hp : p.Monic) (hdeg : p.natDegree = n) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by
  sorry
end PalomarCorpus.E1041.CriticalValueMean

namespace PalomarCorpus.E1041.CubicPath
open Polynomial Set
open scoped BigOperators
/-- The two-segment path from a to b through the hub c, defined for every real t by c + max (1 - t) 0 * (a - c) + max (t - 1) 0 * (b - c) with the real coefficients cast into the complex numbers; it equals a at t = 0, the hub c at t = 1, and b at t = 2, and the clamped coefficients make it continuous and piecewise affine on the whole real line. -/
noncomputable def hub (a c b : ℂ) (t : ℝ) : ℂ :=
  c + ((max (1 - t) 0 : ℝ) : ℂ) * (a - c) +
    ((max (t - 1) 0 : ℝ) : ℂ) * (b - c)
/-- For a monic cubic p presented as the product over i in Fin 3 of (X - C (z i)) whose three listed roots all have modulus strictly below 1, there are distinct indices i, j and a hub c such that hub (z i) c (z j) is continuous, has bounded variation on Icc 0 2, satisfies ‖p.eval (hub (z i) c (z j) t)‖ < 1 for every t in Icc 0 2, and has extended variation strictly below ENNReal.ofReal 2; a second existential gives some curve γ continuous on Icc 0 2 with γ 0 = z i, γ 2 = z j and the same containment and variation bounds, without asserting that γ is that hub path; and Squarefree p implies z i ≠ z j. This is the complete degree-three case of the parent problem in its root-occurrence reading. -/
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by
  sorry
/-- The same degree-three theorem with the cubic given by monicity and degree in place of a root list: for monic p of natural degree 3 every zero of which has modulus strictly below 1, there are zeros a and b of p and a hub c such that hub a c b is continuous, has bounded variation on Icc 0 2, satisfies ‖p.eval (hub a c b t)‖ < 1 for every t in Icc 0 2, and has extended variation strictly below ENNReal.ofReal 2; a second existential gives some curve γ continuous on Icc 0 2 with γ 0 = a, γ 2 = b and the same bounds, without asserting that γ is that hub path. Squarefree p gives a ≠ b; without it a and b may coincide, the degenerate repeated-root case joined by a constant path. -/
theorem monic_cubic_connector (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1) :
    ∃ a b c : ℂ, p.eval a = 0 ∧ p.eval b = 0 ∧
      Continuous (hub a c b) ∧
      BoundedVariationOn (hub a c b) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub a c b t)‖ < 1) ∧
        eVariationOn (hub a c b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = a ∧ γ 2 = b ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → a ≠ b) := by
  sorry
/-- Translated cubic quotient fibres. Let `q ≥ 2`, let `h` be a complex centre and let `P` be a monic complex polynomial of natural degree 3. Suppose every zero `z` of `z ↦ P.eval ((z - h) ^ q)` has modulus strictly below 1, and that this function has two distinct zeros. Then it has two distinct zeros `a` and `b` such that the two-segment path `hub a h b` from `a` through the centre `h` to `b` satisfies `‖P.eval ((hub a h b t - h) ^ q)‖ < 1` for every `t` in `Icc 0 2` and has extended variation strictly below `ENNReal.ofReal 2` on `Icc 0 2`. The factorisation of `P`, the bounds on its roots and the choice of the two zeros are derived in the proof; none of them is a hypothesis. -/
theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖P.eval ((hub a h b t - h) ^ q)‖ < 1) ∧
      eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2 := by
  sorry
end PalomarCorpus.E1041.CubicPath

namespace PalomarCorpus.E1041.CyclicTrinomialFiber
/-- Exact identity eliminating the middle coefficient of a trinomial at one of its roots: if w satisfies w ^ m + a * w ^ r + c = 0 then for every real u the value of z ↦ z ^ m + a * z ^ r + c at the point u * w equals (1 - u ^ r) * c - (u ^ r - u ^ m) * w ^ m, with the real coefficients cast into the complex numbers. No inequality on u, on the natural exponents m and r, or on a, c and w is assumed. -/
theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry
/-- If r ≤ m, w is a root of z ^ m + a * z ^ r + c with ‖w‖ ^ m ≤ ‖c‖, and u lies in [0, 1], then the trinomial has modulus at most ‖c‖ at the point u * w, so the whole spoke from the origin to such a root lies in the closed sublevel set of the constant term, that is in {|f| ≤ |f 0|}. The middle coefficient a is unrestricted, and the root hypothesis ‖w‖ ^ m ≤ ‖c‖ is an extra condition that the open-unit-disc hypothesis of the parent problem does not supply. -/
theorem trinomialRoot_spoke_norm_le_constant
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ ≤ ‖c‖ := by
  sorry
/-- Strict unit-lemniscate form of the preceding bound: adding ‖c‖ < 1 to the hypotheses r ≤ m, w a root of z ^ m + a * z ^ r + c, ‖w‖ ^ m ≤ ‖c‖ and u in [0, 1] gives modulus strictly below 1 at u * w, so the whole spoke of such a root lies in the open unit lemniscate. -/
theorem trinomialRoot_spoke_norm_lt_one
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  sorry
/-- The form reaching every root of the trinomial: for 1 ≤ r ≤ m, a root w of z ^ m + a * z ^ r + c with ‖w‖ < 1, a constant term with ‖c‖ < 1, and u in [0, 1], the trinomial has modulus strictly below 1 at u * w. Every root of modulus below 1 of a trinomial with 1 ≤ r ≤ m and ‖c‖ < 1 therefore supplies a complete radial displacement whose image stays strictly inside the unit lemniscate, with the middle coefficient a unrestricted. -/
theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  sorry
/-- Supporting metric step for the fibre assembly: two complex numbers of modulus strictly below 1 have moduli summing to strictly less than 2, which is the length threshold of the parent problem. -/
theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 := by
  sorry
end PalomarCorpus.E1041.CyclicTrinomialFiber

namespace PalomarCorpus.E1041.DegreeSevenCounterexample
open scoped ENNReal
open Polynomial Metric
/-- There exists a monic complex polynomial p of degree seven whose roots all have modulus strictly below 1 and whose root multiset has no repetitions. For any two distinct roots and any map γ : ℝ → ℂ continuous on [0, 1], joining those roots and satisfying |p(γ(t))| < 1 throughout [0, 1], the extended total variation of γ on that interval is strictly greater than 2. This formalises one explicit instance of ani’s construction, including nonrectifiable paths; it does not assert the whole small-parameter family or a Hausdorff-measure formulation. -/
theorem degreeSevenCounterexample :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
          γ 0 = z₁ → γ 1 = z₂ →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) →
          (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
  sorry
end PalomarCorpus.E1041.DegreeSevenCounterexample

namespace PalomarCorpus.E1041.FirstMergeCriticalValueSeparation
/-- The squared-length coefficient C(n, S) = (1 + S) ^ (2 / n) * log (S / (S - 1)) of the critical-value separation estimate, with the natural number n cast to a real in the exponent; the definition constrains neither n nor S. In the intended reading S is the normalised distance separating the remaining critical values from a simple saddle, and the ordinary analytic estimate of the companion paper bounds the squared length of the connector produced at that saddle by 4 * C(n, S). -/
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))
/-- Three exact all-degree threshold regimes stated as one conjunction: C(n, 4) < 1 for every natural n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6. Each cutoff is the first degree at which its inequality holds, since C(2, 4), C(3, 3) and C(5, 2) all exceed 1; those sharpness statements are recorded in the companion paper and are not part of this declaration. -/
theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  sorry
/-- Numerical consumer of the thresholds: for any natural n and any reals S and length, if length ^ 2 ≤ 4 * C(n, S) and C(n, S) < 1, then length < 2. No positivity or sign hypothesis on length is needed. The analytic estimate that produces length ^ 2 ≤ 4 * C(n, S), namely the two-sheeted square-root uniformisation, its univalence, the Bergman segment inequality and the area and capacity bounds, is ordinary mathematics outside this declaration. -/
theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  sorry
end PalomarCorpus.E1041.FirstMergeCriticalValueSeparation

namespace PalomarCorpus.E1041.QuarticQuotientFiber
/-- Elementary real inequality: for reals alpha ≤ 1 and x > 0 and any real d, the power (√(d ^ 2 + x ^ 2)) ^ (alpha - 1) is at most x ^ (alpha - 1), the exponent being nonpositive while √(d ^ 2 + x ^ 2) is at least x. Its geometric role comes from the family, which reads the two sides as root-lift densities, so that the density on an offset line is dominated by the density on the parallel line through the origin. Supporting lemma for the endpoint budget. -/
theorem rootLift_kernel_le_axis {alpha d x : ℝ}
    (halpha : alpha ≤ 1) (hx : 0 < x) :
    (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) := by
  sorry
/-- Elementary exact integral: for reals alpha > 0 and A ≥ 0, alpha times the interval integral of x ^ (alpha - 1) over [0, A] equals A ^ alpha, with real exponents throughout. It is the primitive of the axis majorant of the preceding lemma, and in that reading positivity of alpha is the local integrability condition at a chord crossing the origin. Supporting lemma for the endpoint budget. -/
theorem rootLift_axis_integral {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 ≤ A) :
    alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha := by
  sorry
/-- For a real exponent alpha > 0 and endpoint moduli a and b in [0, 1), the powered budget a ^ alpha + b ^ alpha is strictly less than 2, which is the length threshold of the parent problem. Only positivity of the exponent and endpoint moduli strictly below 1 are assumed, so the entire open range of admissible endpoints is covered. -/
theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    a ^ alpha + b ^ alpha < 2 := by
  sorry
/-- Consumer of the endpoint budget: any real length bounded by a ^ alpha + b ^ alpha, with alpha > 0 and a, b in [0, 1), is strictly less than 2, with no sign hypothesis on length. The geometric lemma for the quartic, the covering-space lift construction and the final path assembly are ordinary mathematics outside this declaration. -/
theorem rootLift_length_lt_two_of_le_endpoint_budget
    {alpha a b length : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ alpha + b ^ alpha) :
    length < 2 := by
  sorry
end PalomarCorpus.E1041.QuarticQuotientFiber

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
