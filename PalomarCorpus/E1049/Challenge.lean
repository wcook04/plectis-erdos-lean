/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős problem #1049: Lambert values at rational bases

Erdős asked whether `F(t) = sum_{n >= 1} 1/(t^n - 1)`, equivalently the divisor
series `sum_{n >= 1} tau(n) t^{-n}`, is irrational at every rational `t > 1`. The
problem is open and the first resistant explicit base is `3/2`. Nothing in this
file proves irrationality of `F` at any base.

## What is stated here

* `ArchimedeanCap`. For integer polynomial pairs with base-uniform quadratic
  degree rate `delta`, coefficient-height rate `h` and exact remainder rate
  `sigma`, the sufficient cutoff satisfies `sigma / (sigma + delta) <= 1/2` and
  the cleared forms tend to zero strictly below that cutoff. With the height
  rate stated for the largest absolute coefficient, the undivided cleared forms
  fail to decay for `1 <= b < a < b^2`. Since `3/2` sits at
  `log 2 / log 3 = 0.63092975...`, the mechanism is capped below its target.
* `HermitePadeNoGo` and `Shared`. In the explicit rectangular two-function
  exponent model the threshold is at most `1/2 - 1/pi^2` on the whole admissible
  cone, with equality only at the classical endpoint `rho = 0`, `sigma = 1`.
* `AdelicHeightBridge`. The exact bracket `2^64 < 3^41 < 2^65`, the resulting
  `3/13` gap and `8/41` charge ceiling at `3/2`, the failure of scalar and
  scalar-plus-border extraction, the `17/41` scalar-ray margin, the sharp
  `130T + 2S` four-jet collision count at bottom depth `41T`, the initial
  monomial `-6 X^(l+1)` of the first transformed row in every column, two
  division-free closed forms, and, for Zudilin's normalised Hankel determinant
  (his construction, Acta Arith. 111 (2004); Res. Number Theory 2 (2016),
  Art. 15), the order `N(N-1)(2N-1)/6` and the leading coefficient
  `(N!)^2 (N+1)! / 2^N` at every rank `N`.
* `PrimeSupportSelectors`. Sharp `1/q` separation for nonvanishing integral
  linear forms at a rational target, no joint decay of two rows with nonzero
  exterior determinant, determinant-height tradeoffs, and prime-support
  specialisations.
* `RationalBaseBarrier`. The exact cleared-tail recurrence, the `2^(N+1)`
  forcing bound, and impossibility of the coordinatewise clearing corridor
  at `3/2`.
* `BezoutPluckerJets`. Minor propagation and the halved `S + 2R` selector
  threshold, each under a minor-vanishing hypothesis that is not established
  here for any actual approximation family.
* `PublishedHeightRegions`. `3^81 < 2^200`, so `3/2` lies outside the `81/200`
  threshold and outside the published Bundschuh-Vaananen region. The
  Bundschuh and Vaananen region is the published one; the `81/200` region is
  this entry's own elementary sub-boundary and carries no analytic hypothesis. Membership is
  applicability of a method rather than an irrationality statement.
-/

open Polynomial
open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter

namespace PalomarCorpus.E1049.Shared
/-- The cyclotomic saving exponent 3 sigma^2 / pi^2 of the rectangular two-function Hermite-Pade exponent model: the normalised logarithmic size of the common cyclotomic factor removable from a pair of approximation polynomials at model parameter sigma, the constant 3/pi^2 being the mean density in the summatory totient estimate. Reading sigma as a degree parameter is an interpretation, and no statement here uses it. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- The decay exponent (1 + rho^2)/2 + sigma of that model: the normalised rate at which the remainder of the two-function approximation shrinks, in the two real parameters rho and sigma. Reading rho as the rectangularity parameter of the multi-index and sigma as the degree parameter is an interpretation; the statements below use only the formula and the admissible region rho >= 0, sigma >= 1 + rho. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- The height exponent (1 + rho)^2/2 + sigma (1 + rho) of that model: the normalised logarithmic cost of clearing denominators, at the same parameters rho and sigma. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- The threshold (hpDecay - hpCyclotomicSaving) / (hpHeight + hpDecay) delivered by the model at parameters (rho, sigma): the cutoff on the ratio log b / log a below which the decay of this exponent model beats its clearing cost at the rational base a/b. It is a quantity attached to an exponent model and is not itself an irrationality criterion. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
end PalomarCorpus.E1049.Shared

namespace PalomarCorpus.E1049.AdelicHeightBridge
open Polynomial
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
/-- The homogeneous evaluation H_W(P) = sum over 0 <= i <= W of (coefficient of X^i in P) times 3^i times 2^(W - i), an integer attached to an integer polynomial P and a declared width W; it equals 2^W P(3/2) when the degree of P is at most W. It is linear in P. Coefficients of P in degrees above W are discarded, so the value depends on the declared width and not on P alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
/-- The bottom jet of P at depth R: the residue class of the homogeneous evaluation H_W(P) in the ring of integers modulo 3^R, 3 being the numerator of the base. It vanishes exactly when 3^R divides H_W(P). -/
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
/-- The top jet of P at depth S: the residue class of the homogeneous evaluation H_W(P) in the ring of integers modulo 2^S, 2 being the denominator of the base. It vanishes exactly when 2^S divides H_W(P). -/
noncomputable def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P
/-- The finite abelian group (Z/3^R Z)^2 times (Z/2^S Z)^2 in which four-jet signatures of a pair of integer polynomials live; its cardinality is 3^(2R) 2^(2S). -/
noncomputable abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))
/-- The four-jet signature of a pair (U, V) of integer polynomials at declared width W: the quadruple formed by the bottom jets of U and of V modulo 3^R together with the top jets of U and of V modulo 2^S. All four entries vanish exactly when 3^R 2^S divides both homogeneous evaluations H_W(U) and H_W(V). -/
noncomputable def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))
/-- The signature of the subfamily picked out by a Boolean vector: given n polynomial pairs and a function from the index set to Bool, the sum in the signature group of the four-jet signatures of the selected pairs. Since the homogeneous evaluation is linear, this is the signature of the summed pair. -/
noncomputable def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0
/-- The finite q-Pochhammer product (q^start; q)_len, that is the product over 0 <= r < len of (1 - q^(start + r)), as a formal power series over the integers in the variable q; the empty product at len = 0 is 1. -/
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)
/-- The unit factor of the t-th summand of Zudilin's normalised moment of index n: the power series (q;q)_n^3 (q^(t+1);q)_n divided by (q^(n+1+t);q)_(n+1). The division is the formal inverse of a power series whose constant term is 1, which holds here because every factor of the divisor has positive exponent. -/
noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1
/-- The exact t-th summand q^((n+1)t) (q;q)_n^3 (q^(t+1);q)_n / (q^(n+1+t);q)_(n+1) of Zudilin's normalised moment of index n, a formal power series of order (n+1)t in q. -/
noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t
/-- Zudilin's normalised moment of index n, the sum over t >= 0 of the summands above, defined coefficientwise: the coefficient of q^d is the finite sum over t <= d/(n+1) of the degree-d coefficients of those summands. That finite sum is the whole sum, because the t-th summand has order (n+1)t. -/
noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)
/-- The first nontrivial backward difference of the normalised moments in column l, that is the moment of index l + 1 minus the moment of index l; it is the entry in column l of the depth-one row produced by the backward-difference row transformation of the moment matrix. -/
noncomputable def zudilinFirstTransformedRow (l : ℕ) : PowerSeries ℤ :=
  zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l
/-- For every column index l, the entry of the first transformed row in that column has power series order exactly l + 1, the order being pinned to that finite value in the extended naturals, and coefficient exactly -6 in that degree, so its initial monomial is -6 q^(l+1). The statement is unconditional and holds in every column at depth one. It asserts nothing about transformed rows of depth two or more, and it does not by itself determine the order of the associated Hankel determinant. -/
theorem zudilin_firstTransformedRow_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinFirstTransformedRow l) = l + 1 ∧
      PowerSeries.coeff (l + 1) (zudilinFirstTransformedRow l) = -6 := by
  sorry
/-- The integer sum over j < N of j^2, written as a sum of squares; it equals N(N-1)(2N-1)/6. The same sum taken in the natural numbers is the order that zudilinSharpHankelOrderAndCoeff_all below proves for the normalised Hankel determinant of rank N. The definition is that sum alone; it names no determinant and asserts no order. -/
noncomputable def zudilinSharpHankelQOrder (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, (j : ℤ) ^ 2
/-- The natural number (j+1)^2 (j+2)/2, the magnitude of the leading coefficient contributed by the transformed row of depth j; the natural-number division by 2 is exact because (j+1)^2 (j+2) is always even. -/
noncomputable def zudilinTransformedRowCoeff (j : ℕ) : ℕ :=
  ((j + 1) ^ 2 * (j + 2)) / 2
/-- Two division-free closed forms for the assembled Hankel data: six times the sum over j < N of j^2 equals N(N-1)(2N-1), and 2^N times the product over j < N of (j+1)^2 (j+2)/2 equals (N!)^2 (N+1)!. The first identity is read over the integers after casting N, so N - 1 is -1 at N = 0; both hold for every natural N, including the degenerate cases N = 0 and N = 1. This is an algebraic identity about the assembled quantities and identifies no formal power series determinant with them; the order and leading coefficient of the normalised Hankel determinant are stated by zudilinSharpHankelOrderAndCoeff_all and coeff_zudilinNormalizedHankelDet_all_rat below. -/
theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) :
    6 * zudilinSharpHankelQOrder N =
        (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧
      2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
        (N.factorial) ^ 2 * (N + 1).factorial := by
  sorry
/-- The N by N Hankel matrix of a sequence v of formal power series over the integers: the entry in row j and column l is v (j + l), for j and l below N. -/
noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))
/-- Zudilin's normalised Hankel determinant V_N^* at x = z = 1: the determinant of the N by N Hankel matrix of the normalised moments above, a formal power series over the integers in q, equal to 1 at N = 0. The normalised moments and this determinant are Zudilin's construction (Acta Arith. 111 (2004); Res. Number Theory 2 (2016), Art. 15). -/
noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det
/-- For every natural N, the normalised Hankel determinant of rank N has power series order equal to the sum over j < N of j^2, which is N(N-1)(2N-1)/6, pinned to that finite value in the extended naturals, and its coefficient in that degree equals the product over j < N of (j+1)^2 (j+2)/2. There is no hypothesis on N, and N = 0 is included, where the determinant is 1. Zudilin proves that the order is at least N(N-1)(2N-1)/6 (Res. Number Theory 2 (2016), Art. 15, Section 4); the moments and the determinant are his construction. -/
theorem zudilinSharpHankelOrderAndCoeff_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
        ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) ∧
      PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
          (zudilinNormalizedHankelDet N) =
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
  sorry
/-- For every natural N, the coefficient of q^(N(N-1)(2N-1)/6) in the normalised Hankel determinant of rank N, cast from the integers to the rationals, equals (N!)^2 (N+1)! / 2^N. The degree is written with natural-number subtraction and division, which lose nothing here: the subtractions truncate only at N = 0, where the degree is 0 either way, and 6 divides N(N-1)(2N-1). By the previous theorem this degree is the order of the determinant, so the value is its leading coefficient. -/
theorem coeff_zudilinNormalizedHankelDet_all_rat (N : ℕ) :
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N := by
  sorry
/-- The exact integer comparison 3^41 < 2^65, equivalently log 3 / log 2 < 65/41. This verified numerical fact is the upper half of the power bracket from which every explicit threshold in this family descends. -/
theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by
  sorry
/-- The exact integer comparison 2^64 < 3^41, the lower half of the same bracket. It shows that the exponent 65 cannot be lowered to 64, so 65 is the least exponent q for which 3^41 < 2^q. -/
theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by
  sorry
/-- For every rho >= 0 and every sigma >= 1 + rho, that is over the whole admissible rectangular exponent cone, the model threshold falls short of log 2 / log 3 by more than 3/13. Reaching the base 3/2 by this model would require a threshold above log 2 / log 3 = 0.63092975..., so no admissible choice of exponents in the model reaches it. The conclusion is about the exponent model and constructs no approximants. -/
theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  sorry
/-- The real inequality (log 3 / log 2 - 1)/3 < 8/41, a consequence of 3^41 < 2^65. It is the surviving-charge threshold at the base 3/2 that fixes the 39/41 denominator-charge comparison below, in which more than 39/41 of the raw power 4N^3 - 3N^2 of the cubic Hankel determinant has to be cleared. -/
theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  sorry
/-- For integers N > 0 and extractedDegree at most N^3 - N, which is the ceiling for the scalar content of the cubic Hankel determinant, one has 41 extractedDegree < 39 (4N^3 - 3N^2). Dividing by 41, the inequality puts extractedDegree strictly below the required 39/41 fraction of the raw denominator power 4N^3 - 3N^2, so scalar content under that ceiling never meets the required charge. The degree ceiling enters as a hypothesis and is not proved here. -/
theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  sorry
/-- The same comparison with the larger ceiling: for integers N >= 2 and extractedDegree at most 2N^3 - N, which covers scalar content together with the forced first-order residual border, one still has 41 extractedDegree < 39 (4N^3 - 3N^2). The combined ceiling is a hypothesis and is not proved here. -/
theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  sorry
/-- For real C0 > 0 and C1 with 2 C0 <= C1, the balance C0 log 3 - C1 log 2 is strictly below -(17/41) C0 log 2. The hypothesis 2 C0 <= C1 is the elementary consequence of an integer-base irrationality exponent at least 2, so every scalar parameter pair on that ray misses the balance needed at 3/2 by the fixed relative margin 17/41. -/
theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 <
      -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  sorry
/-- Let forms be any n pairs of integer polynomials, let W be any width, let T > 0, and let 3^p < 2^q be any integer power certificate. If n >= 2qT + 2S then two distinct Boolean selectors have the same four-jet signature sum at bottom depth pT and top depth S. Every such certificate therefore lowers the generic collision threshold 4pT + 2S to 2qT + 2S. The statement gives no information about whether the corresponding difference of selected pairs is a nonzero pair of polynomials. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    {n p q T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hpq : (3 : ℕ) ^ p < (2 : ℕ) ^ q) (hT : 0 < T)
    (hrank : 2 * q * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (p * T) S W forms ε =
        selectedFourJetSum (p * T) S W forms η := by
  sorry
/-- The specialisation of the previous theorem at p = 41 and q = 65: for T > 0 and any family of n >= 130T + 2S pairs of integer polynomials, two distinct Boolean selectors have the same four-jet signature sum at bottom depth 41T and top depth S. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε =
        selectedFourJetSum (41 * T) S W forms η := by
  sorry
/-- For every S, the number 2^(129 + 2S) is strictly smaller than the cardinality of the four-jet signature group at bottom depth 41 and top depth S. So 129 + 2S selectors fail the counting inequality and the coefficient 130 of the previous theorem is exact at T = 1 for this counting argument. A family with fewer rows may still collide for other reasons. -/
theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  sorry
/-- Bounded-fibre pigeonhole. For a finite type alpha, a finite type beta, maps f from alpha to beta and g from alpha to a type with decidable equality, if every fibre of g has at most k elements and (card beta) times k is less than card alpha, then some two distinct elements of alpha have equal f value and different g value. Taking f the four-jet signature sum and g the analytic remainder, a uniform remainder multiplicity bound converts a signature collision into one outside the remainder nullspace. -/
theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  sorry
end PalomarCorpus.E1049.AdelicHeightBridge

namespace PalomarCorpus.E1049.ArchimedeanCap
open Filter Asymptotics
open scoped Topology
/-- The declared clearing width of the n-th approximation pair: the larger of the degrees of the polynomials U n and V n, as a natural number. Under the Mathlib convention the zero polynomial has degree zero. -/
noncomputable def width (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ := max (U n).natDegree (V n).natDegree
/-- The l^1 coefficient norm of an integer polynomial, the sum over its support of the absolute values of its coefficients, returned as a real number; the zero polynomial has empty support and height 0. -/
noncomputable def height (P : Polynomial ℤ) : ℝ := ∑ i ∈ P.support, |(P.coeff i : ℝ)|
/-- The remainder U_n(x) F(x) - V_n(x) of the n-th pair at the real point x, the polynomials being evaluated through the canonical ring map from the integers to the reals. Here F is an arbitrary real function supplied as a parameter rather than a fixed Lambert series. -/
noncomputable def remainder (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x - (V n).eval₂ (Int.castRingHom ℝ) x
/-- Archimedean cap. Let U, V be sequences of integer polynomials, F any real function, and fix sigma > 0, delta > 0, h >= 0 not depending on the evaluation point. Assume for each eps > 0 that the width is eventually at most (delta + eps) n^2 and the logarithm of the larger l^1 coefficient norm eventually at most (h + eps) n^2; that at each real x > 1 the remainder is eventually nonzero; and that at each real x > 1 the quantity log |remainder| + sigma n^2 log x is o(n^2). Then sigma/(sigma + delta) <= 1/2, and for all naturals 1 <= b < a with log b / log a < sigma/(sigma + delta) the forms b^(width n) times the remainder at a/b tend to zero. -/
theorem archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (max (height (U n)) (height (V n))) ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ width U V n * remainder U V F ((a : ℝ) / b) n)
        atTop (𝓝 0) := by
  sorry
/-- The l^infinity coefficient norm of an integer polynomial as a natural number: the supremum over its support of the absolute values of its coefficients, which is 0 for the zero polynomial. -/
noncomputable def maxCoefficient (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)
/-- Under the same base-uniform hypotheses as the cap, with the height rate stated for the largest absolute coefficient instead of the l^1 norm, for naturals a and b with 1 <= b and b < a < b^2 the undivided forms b^(width n) times the remainder at a/b do not tend to zero. No limit of the normalised width is assumed, the boundary case a = b^2 is not classified, and the conclusion concerns the undivided forms rather than constructions that first divide by base-dependent content. -/
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log ((max (maxCoefficient (U n)) (maxCoefficient (V n)) : ℕ) : ℝ)
        ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ width U V n *
      remainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E1049.ArchimedeanCap

namespace PalomarCorpus.E1049.BezoutPluckerJets
open scoped BigOperators
/-- Let w be a family of pairs in a commutative ring R, indexed by any type, and let a and b in R be coprime in the Bezout sense. If the anchor minor a (w i).2 - b (w i).1 vanishes for every index i, then every pairwise minor (w i).1 (w j).2 - (w i).2 (w j).1 vanishes: the whole family lies on the single line cut out by the anchor. -/
theorem anchor_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    {ι : Type*} (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  sorry
/-- Under the hypotheses above with R and the index type both finite, if the cardinality of R is smaller than 2 raised to the number of indices, then two distinct Boolean selectors have the same selected row sum in R times R. The minor collapse confines the selector sums to one copy of R, so the collision threshold is the cardinality of R rather than its square. -/
theorem binary_row_collision_of_anchor_det_zero
    {R ι : Type*} [CommRing R] [Fintype R] [Fintype ι]
    (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0)
    (hcard : Fintype.card R < 2 ^ Fintype.card ι) :
    ∃ s t : ι → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
/-- For a sequence of pairs in a commutative ring whose second coordinates are all units, vanishing of every adjacent minor implies vanishing of every pairwise minor. This is the sequential form of the previous propagation, with a unit coordinate in place of the coprime anchor. -/
theorem adjacent_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    (w : ℕ → R × R) (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  sorry
/-- At the modulus 2^S 3^R with R > 0, let w be a sequence of pairs of residues whose second coordinates are units and whose adjacent minors all vanish. Then for every k >= S + 2R there are two distinct Boolean selectors on k indices with equal selected row sums. The collapse halves the ambient two-coordinate threshold 2S + 4R to S + 2R. The vanishing of every adjacent minor is a hypothesis and is not established here for any actual approximation family. -/
theorem zmod_binary_tail_collision_of_two_three_depth {R S k : ℕ}
    [NeZero (2 ^ S * 3 ^ R)]
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hrank : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
end PalomarCorpus.E1049.BezoutPluckerJets

namespace PalomarCorpus.E1049.HermitePadeNoGo
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
/-- The denominator-cleared comparison functional (pi^2 + 2) hpDecay - 6 sigma^2 - (pi^2 - 2) hpHeight, whose sign decides whether the rectangular two-function threshold of the model exceeds the classical one-function threshold 1/2 - 1/pi^2. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma
/-- Exact polynomial identity after the substitution sigma = 1 + rho + u: the cleared gap equals -pi^2 rho^2 - pi^2 rho u - 2 pi^2 rho - 2 rho^2 - 10 rho u - 4 rho - 6 u^2 - 8 u. The identity holds for all real rho and u; on rho >= 0 and u >= 0 every term is nonpositive. Supporting identity for the two comparison theorems below. -/
theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u := by
  sorry
/-- On the admissible region rho >= 0 and sigma >= 1 + rho the cleared comparison functional is nonpositive. Supporting lemma for the threshold comparison. -/
theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 := by
  sorry
/-- On that same admissible region the cleared comparison functional vanishes if and only if rho = 0 and sigma = 1, the classical one-function endpoint. Supporting lemma for the sharpness statement. -/
theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 := by
  sorry
/-- Over the whole admissible cone rho >= 0 and sigma >= 1 + rho, the rectangular two-function threshold of this explicit exponent model is at most 1/2 - 1/pi^2 = 0.398678816..., the classical one-function value. No admissible choice of exponents in the model improves on the classical threshold. The theorem is about this exponent model only: it constructs no approximants and proves no irrationality statement. -/
theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 := by
  sorry
/-- On the same cone the threshold equals 1/2 - 1/pi^2 if and only if rho = 0 and sigma = 1. The previous bound is therefore sharp and its equality locus is that single point. -/
theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 := by
  sorry
end PalomarCorpus.E1049.HermitePadeNoGo

namespace PalomarCorpus.E1049.PrimeSupportSelectors
open Filter
/-- At a rational target a/q with q > 0, two integral rows whose exterior determinant A_1 B_2 - A_2 B_1 is nonzero cannot both have remainder below 1/q: at least one of |B_1 (a/q) - A_1| and |B_2 (a/q) - A_2| is at least 1/q. Nonvanishing of the determinant is the only hypothesis on the rows; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- At a rational target a/q with q > 0, an integral linear form B (a/q) - A that does not vanish has absolute value at least 1/q. Nonvanishing of the form is the only hypothesis; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- For sequences of integral rows whose exterior determinant is nonzero at every index, the two real linear forms B_1 (a/q) - A_1 and B_2 (a/q) - A_2 cannot both tend to zero at a rational target a/q with q > 0. No such pair of selectors jointly witnesses vanishing at a rational point. -/
theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) := by
  sorry
/-- If two real linear forms at a common real target F have remainders |B_1 F - A_1| and |B_2 F - A_2| at most eps, then their exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= eps (|B_1| + |B_2|), so joint decay is paid for in determinant size. The statement is about real data and uses no change of basis, no integrality and no coefficient-height hypothesis. -/
theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by
  sorry
/-- If a real two by two recombination with |u z - v w| = 1 and all four entries bounded in absolute value by H makes both recombined remainders at most eps >= 0 at a common real target F, then the original exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= 2 H eps (|B_1| + |B_2|). Joint decay reached through a bounded change of basis is still paid for in determinant size; integer unimodular recombination is a special case. -/
theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) := by
  sorry
/-- Let ell be prime, let q > 0 with ell not dividing q, let ell divide both B_1 and B_2, and let ell^2 not divide A_1 B_2 - A_2 B_1. Then at least one of the two rows has the full gap 1/q at the target a/q. This is the arithmetic-facing specialisation of the two-row gap: the hypothesis on ell^2 already forces the determinant to be nonzero, and the prime data records the divisibility interface an approximation family would have to supply. -/
theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- Let ell be prime with ell dividing B, ell not dividing A, and ell not dividing q > 0. Then |B (a/q) - A| >= 1/q. The prime data certifies the nonvanishing that the unconditional one-row gap takes as a hypothesis. -/
theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- The same conclusion |B (a/q) - A| >= 1/q under prime-power support: ell prime, r nonzero, ell^r dividing B, ell not dividing A, and ell not dividing q > 0. A single copy of ell already suffices for the conclusion; the stronger hypothesis is retained so that a tail exponent can be passed through unchanged. -/
theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- If the second coordinate of each of k pairs of residues modulo N vanishes, then N < 2^k already forces two distinct Boolean selectors with equal selected sums in both coordinates. With one coordinate identically zero the pigeonhole only has to see the other, so the threshold is N rather than N^2. -/
theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions
/-- The parameter region log b / log a < 1/2 - 1/pi^2 of the published Bundschuh-Vaananen criterion, written for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This records only the elementary parameter inequality; their analytic irrationality theorem is not internalised, so membership is applicability of a method rather than an irrationality statement. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- The parameter region log b / log a < 81/200 for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This threshold is defined here as an elementary sub-boundary of the region reached by the project's separate ordinary rational-base theorem; it is not a published criterion and carries no analytic hypothesis. -/
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
/-- The exact integer comparison 3^81 < 2^200, the verified numerical fact that places the base 3/2 beyond the 81/200 threshold. -/
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 := by
  sorry
/-- The real inequality 81/200 < log 2 / log 3, obtained by taking logarithms in the integer comparison above. -/
theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 := by
  sorry
/-- The base 3/2 does not satisfy log 2 / log 3 < 81/200, so it lies outside the region defined above. This is a boundary of method applicability; it proves neither rationality nor irrationality of the corresponding Lambert value. -/
theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  sorry
/-- The base 3/2 also lies outside the Bundschuh-Vaananen region, since 1/2 - 1/pi^2 = 0.398678816... is below 81/200 and log 2 / log 3 = 0.63092975... already exceeds the larger threshold. Inapplicability of that published criterion proves neither rationality nor irrationality. -/
theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  sorry
end PalomarCorpus.E1049.PublishedHeightRegions

namespace PalomarCorpus.E1049.RationalBaseBarrier
open scoped BigOperators
/-- The finite arithmetic core of one coordinatewise clearing scheme at the base a/b: the conjunction of a > 0, Q > 0, 0 < digit <= N + K, the divisibility a^K dividing Q times digit, and the tail inequality Q b^(N+K+1) < a^(K+1). Here Q is the accumulated clearing factor and digit the coefficient being cleared, while N and K are the two window parameters: K is the exponent of a in the divisibility and K + 1 its exponent in the tail inequality, N + K bounds digit, and N + K + 1 is the exponent of b. The bound digit <= N + K is the only property of that coefficient used. -/
noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)
/-- The rational number formed by the first N coordinates of the divisor-style series at the rational base r/s: the sum over 0 <= m < N of coeff(m+1) s^(m+1) / r^(m+1). -/
noncomputable def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)
/-- The denominator-cleared tail state B r^N (F - prefix_N) attached to a putative value F of the series at the rational base r/s, where B is the assumed clearing constant and prefix_N is the rational prefix above. -/
noncomputable def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)
/-- The natural number B coeff(N+1) s^(N+1): the magnitude of the forcing term that the cleared-tail recurrence leaves behind at step N, for natural data. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
/-- Exact recurrence for the cleared tail state: for every natural N and every nonzero rational r, the state at N + 1 equals r times the state at N minus B coeff(N+1) s^(N+1). The identity holds for arbitrary rational F and arbitrary coefficient sequence, so the whole clearing scheme is governed by that single forcing term. It is an identity, not a rationality contradiction. -/
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  sorry
/-- For a genuine rational base, meaning denominator s >= 2, together with B >= 1 and coeff(N+1) >= 1, the forcing term is at least 2^(N+1). The hypothesis s >= 2 is what separates a rational base from an integer base, where the factor s^(N+1) is 1 and the classical coordinatewise argument survives. -/
theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  sorry
/-- At the base 3/2 no coordinatewise corridor exists: for all naturals N >= 1 and K >= 1 and all naturals Q and digit, the tuple (3, 2, N, K, Q, digit) fails the corridor conditions. The divisibility caps 3^K by Q(N + K) while the tail inequality demands Q 2^(N+K+1) < 3^(K+1), and an exponential quantity cannot sit below a linear one. This excludes one named clearing scheme at 3/2 and nothing else; it bounds no denominator and decides no irrationality. -/
theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  sorry
end PalomarCorpus.E1049.RationalBaseBarrier
