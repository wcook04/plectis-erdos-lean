/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_03

Every non-theorem declaration of `PalomarCorpus/E1049_03/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1049.PaperStatementsK

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
export PalomarCorpus.E1049_03.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
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
/-- The integer sum over j < N of j^2, written as a sum of squares; it equals N(N-1)(2N-1)/6. The same sum taken in the natural numbers is the order that zudilinSharpHankelOrderAndCoeff_all below proves for the normalised Hankel determinant of rank N. The definition is that sum alone; it names no determinant and asserts no order. -/
noncomputable def zudilinSharpHankelQOrder (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, (j : ℤ) ^ 2
/-- The natural number (j+1)^2 (j+2)/2, the magnitude of the leading coefficient contributed by the transformed row of depth j; the natural-number division by 2 is exact because (j+1)^2 (j+2) is always even. -/
noncomputable def zudilinTransformedRowCoeff (j : ℕ) : ℕ :=
  ((j + 1) ^ 2 * (j + 2)) / 2
/-- The N by N Hankel matrix of a sequence v of formal power series over the integers: the entry in row j and column l is v (j + l), for j and l below N. -/
noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))
/-- Zudilin's normalised Hankel determinant V_N^* at x = z = 1: the determinant of the N by N Hankel matrix of the normalised moments above, a formal power series over the integers in q, equal to 1 at N = 0. The normalised moments and this determinant are Zudilin's construction (Acta Arith. 111 (2004); Res. Number Theory 2 (2016), Art. 15). -/
noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det
end PalomarCorpus.E1049.AdelicHeightBridge
