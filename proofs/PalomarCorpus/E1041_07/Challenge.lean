/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, the critical geometry, cyclic trinomial fiber and degree seven counterexample families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Finset
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
