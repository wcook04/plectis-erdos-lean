/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049

Every non-theorem declaration of `PalomarCorpus/E1049/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
/-- The l^infinity coefficient norm of an integer polynomial as a natural number: the supremum over its support of the absolute values of its coefficients, which is 0 for the zero polynomial. -/
noncomputable def maxCoefficient (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)
end PalomarCorpus.E1049.ArchimedeanCap

namespace PalomarCorpus.E1049.BezoutPluckerJets
open scoped BigOperators
end PalomarCorpus.E1049.BezoutPluckerJets

namespace PalomarCorpus.E1049.HermitePadeNoGo
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)
/-- The denominator-cleared comparison functional (pi^2 + 2) hpDecay - 6 sigma^2 - (pi^2 - 2) hpHeight, whose sign decides whether the rectangular two-function threshold of the model exceeds the classical one-function threshold 1/2 - 1/pi^2. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma
end PalomarCorpus.E1049.HermitePadeNoGo

namespace PalomarCorpus.E1049.PrimeSupportSelectors
open Filter
end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions
/-- The parameter region log b / log a < 1/2 - 1/pi^2 of the published Bundschuh-Vaananen criterion, written for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This records only the elementary parameter inequality; their analytic irrationality theorem is not internalised, so membership is applicability of a method rather than an irrationality statement. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- The parameter region log b / log a < 81/200 for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This threshold is defined here as an elementary sub-boundary of the region reached by the project's separate ordinary rational-base theorem; it is not a published criterion and carries no analytic hypothesis. -/
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
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
end PalomarCorpus.E1049.RationalBaseBarrier
