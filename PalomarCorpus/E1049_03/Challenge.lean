/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, record sections 3 to 5; the adelic height bridge family: power comparisons and Hankel determinants; congruences after evaluation at 3/2

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open scoped BigOperators
open Polynomial
open Filter Asymptotics
open scoped Topology
open Filter

namespace PalomarCorpus.E1049_03.Shared
/-- The cyclotomic saving exponent 3 sigma^2 / pi^2 of the rectangular two-function Hermite-Pade exponent model: the normalised logarithmic size of the common cyclotomic factor removable from a pair of approximation polynomials at model parameter sigma, the constant 3/pi^2 being the mean density in the summatory totient estimate. Reading sigma as a degree parameter is an interpretation, and no statement here uses it. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- The decay exponent (1 + rho^2)/2 + sigma of that model: the normalised rate at which the remainder of the two-function approximation shrinks, in the two real parameters rho and sigma. Reading rho as the rectangularity parameter of the multi-index and sigma as the degree parameter is an interpretation; the statements below use only the formula and the admissible region rho >= 0, sigma >= 1 + rho. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- The height exponent (1 + rho)^2/2 + sigma (1 + rho) of that model: the normalised logarithmic cost of clearing denominators, at the same parameters rho and sigma. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- Rational-base height threshold associated with the explicit exponent model above. Local copy of ErdosProblems.Erdos1049.hpThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
end PalomarCorpus.E1049_03.Shared

namespace PalomarCorpus.E1049.PaperStatementsK
open scoped BigOperators
/-- States long1049:res:chargeceilings from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.charge_ceilings in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem charge_ceilings :
    (∀ N : ℤ, 0 < N →
      41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N : ℤ, 2 ≤ N →
      41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 0 < N → E ≤ N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 2 ≤ N → E ≤ 2 * N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) := by
  sorry
/-- States long1049:res:powerbracket from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.power_bracket in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem power_bracket :
    (2 : ℕ) ^ 64 < 3 ^ 41 ∧ 3 ^ 41 < 2 ^ 65 ∧
      (41 : ℝ) / 65 < Real.log 2 / Real.log 3 ∧
      Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := by
  sorry
end PalomarCorpus.E1049.PaperStatementsK

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
export PalomarCorpus.E1049_03.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
/-- States long1049:res:sharpgaps from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.height_and_hankel_deficits in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem height_and_hankel_deficits (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) ∧
      (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma ∧
      (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  sorry
end PalomarCorpus.E1049.PaperStatementsN

namespace PalomarCorpus.E1049.AdelicHeightBridge
open Polynomial
open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter
open Polynomial
export PalomarCorpus.E1049_03.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
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
