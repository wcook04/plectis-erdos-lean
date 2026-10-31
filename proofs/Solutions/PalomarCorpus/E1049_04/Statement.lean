/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_04

Every non-theorem declaration of `PalomarCorpus/E1049_04/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Matrix
open Polynomial
open Filter
open Topology
open Finset

namespace PalomarCorpus.E1049_04.Shared
/-- Local copy of ErdosProblems.Erdos1049.AllRow.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S := PowerSeries ℤ
/-- A finite ratio with constant term one in the state variable. Local copy of ErdosProblems.Erdos1049.AllRow.finiteRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))
/-- `H(q^{n+1}) = 1 + ∑_{s ≥ 1} a_s(q) q^{(n+1)s}`, the untruncated ratio. Each coefficient is the corresponding coefficient of a long enough truncation, which is exactly what the infinite sum means: the term of index `s` has order at least `s + 1`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)
/-- `H̄ = H mod q`, an ordinary power series in `X` over `ℤ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReducedSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)
/-- `h_r = [X^r] H̄(X)^{-1}`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)
end PalomarCorpus.E1049_04.Shared

namespace PalomarCorpus.E1049.PaperStatementsG
open scoped BigOperators
/-- Hankel matrix of an arbitrary power-series moment sequence. Local copy of ErdosProblems.Erdos1049.zudilinMomentMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))
/-- Finite `q`-Pochhammer product `(q^start;q)_len`, represented as an integer formal power series. Local copy of ErdosProblems.Erdos1049.zudilinPochhammerPS, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)
/-- The unit factor in the `t`th normalized summand `(q;q)_n^3(q^(t+1);q)_n/(q^(n+1+t);q)_(n+1)`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedTailUnit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1
/-- The exact `t`th summand of Zudilin's normalized moment `v_n^*` at `x=z=1`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t
/-- Zudilin's normalized moment `v_n^*` as a genuine formal power series. For each coefficient `q^d`, only tails `t≤d/(n+1)` can contribute, so the source infinite sum is defined coefficientwise by this exact finite sum. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)
/-- Zudilin's normalized Hankel determinant `V_N^*`. Local copy of ErdosProblems.Erdos1049.zudilinNormalizedHankelDet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det
end PalomarCorpus.E1049.PaperStatementsG

namespace PalomarCorpus.E1049.PaperStatementsB
open scoped BigOperators
export PalomarCorpus.E1049_04.Shared (S finiteRatio paperRatio paperReciprocal paperReducedSeries)
/-- Equality of all coefficients strictly below `D`. Local copy of ErdosProblems.Erdos1049.AllRow.Agree, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Agree (D : ℕ) (f g : S) : Prop :=
  ∀ d, d < D → PowerSeries.coeff d f = PowerSeries.coeff d g
/-- Row exponent in a form compatible with the canonical row proposition. Local copy of ErdosProblems.Erdos1049.AllRow.rowExponent, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowExponent (j l : ℕ) : ℕ := j * (j + 1) / 2 + j * l
end PalomarCorpus.E1049.PaperStatementsB

namespace PalomarCorpus.E1049.PaperStatementsH
open scoped BigOperators
export PalomarCorpus.E1049_04.Shared (S finiteRatio paperRatio paperReciprocal paperReducedSeries)
/-- `∏_{r=1}^{m} H(q^r)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperUnit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperUnit (a : ℕ → S) : ℕ → S
  | 0 => 1
  | n + 1 => paperUnit a n * paperRatio a n
/-- `W_m(t) = q^{(m+1)t} ∏_{r=1}^{m} H(q^r)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperTail (a : ℕ → S) (n t : ℕ) : S :=
  PowerSeries.X ^ ((n + 1) * t) * paperUnit a n
/-- Gaussian binomial coefficients as integer power series, using the standard Pascal recurrence. This is the coefficient occurring in Zudilin's displayed operator `D_j=(N;q)_j`. Local copy of ErdosProblems.Erdos1049.zudilinQBinomialPS, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinQBinomialPS : ℕ → ℕ → PowerSeries ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => zudilinQBinomialPS n (k + 1) +
      PowerSeries.X ^ (n - k) * zudilinQBinomialPS n k
/-- Coefficient of the `k`th backward shift in the source operator `D_j=(N;q)_j`: `(-1)^k q^(k(k-1)/2) [j choose k]_q`. Local copy of ErdosProblems.Erdos1049.zudilinBackwardShiftCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinBackwardShiftCoeff (j k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((-1 : ℤ) ^ k) *
    PowerSeries.X ^ (k * (k - 1) / 2) * zudilinQBinomialPS j k
/-- Apply the source operator `D_j` to the `n`th term of an arbitrary power-series sequence. The range is finite and agrees literally with the displayed Gaussian-binomial expansion in Zudilin's source. Local copy of ErdosProblems.Erdos1049.zudilinBackwardShiftApply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinBackwardShiftApply
    (j n : ℕ) (v : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    zudilinBackwardShiftCoeff j k * v (n - k)
end PalomarCorpus.E1049.PaperStatementsH

namespace PalomarCorpus.E1049.PaperStructuresO
open Matrix
open Polynomial
open scoped BigOperators
open Filter
open Topology
open Finset
/-- Local definition lambertTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)
/-- Local definition lambert, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n
/-- Local definition coefficientQFactorialPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientQFactorialPoly (m : ℕ) : ℤ[X] :=
  ∏ j ∈ range m, ∑ i ∈ range (j + 1), X ^ i
/-- Local definition gaussBinom, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0
/-- Local definition coefficientRPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientRPoly (m : ℕ) : ℤ[X] :=
  ∑ k ∈ range (m + 1),
    C ((-1 : ℤ) ^ (m + k)) * X ^ (k * (k + 1) / 2) *
      gaussBinom X m k * gaussBinom X (m + k) k
/-- Local definition coefficientMomentPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientMomentPoly (m : ℕ) : ℤ[X] :=
  coefficientQFactorialPoly m ^ 3 * coefficientRPoly m
/-- Local definition coefficientAlphaPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientAlphaPoly (m : ℕ) : ℤ[X] :=
  X * (X * (X - 1) ^ 3) ^ m * coefficientMomentPoly m
/-- Local definition coefficientAlpha, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientAlpha (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientAlphaPoly m).eval₂ (Int.castRingHom ℝ) p
/-- Local definition coefficientAlphaMatrix, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientAlphaMatrix (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => coefficientAlpha p (i.val + j.val)
/-- Local definition divisorCount, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def divisorCount (j : ℕ) : ℤ := (Nat.divisors j).card
/-- Local definition lambertPolynomialPart, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertPolynomialPart (P : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ range (P.natDegree + 1),
    C (P.coeff i) * ∑ r ∈ range i, C (divisorCount (i - r)) * X ^ r
/-- Local definition coefficientBetaPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientBetaPoly (m : ℕ) : ℤ[X] :=
  lambertPolynomialPart (coefficientAlphaPoly m) - 1
/-- Local definition coefficientBeta, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientBeta (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientBetaPoly m).eval₂ (Int.castRingHom ℝ) p
/-- Local definition coefficientPencilPoly, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coefficientPencilPoly (p : ℝ) (N : ℕ) : ℝ[X] :=
  Matrix.det (Matrix.of fun i j : Fin N =>
    X * C (coefficientAlpha p (i.val + j.val)) -
      C (coefficientBeta p (i.val + j.val)))
end PalomarCorpus.E1049.PaperStructuresO

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
/-- The real error of an integer Padé coefficient pair `(U,V)` at `S`. Local copy of ErdosProblems.Erdos1049.rationalPadeError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeError (S : ℝ) (U V : ℤ) : ℝ :=
  (U : ℝ) * S - (V : ℝ)
/-- The exterior determinant of two integer Padé coefficient pairs. For the adjacent Zudilin construction this is `Uₙ Vₘ - Uₘ Vₙ`. Unlike either individual coefficient pair, the determinant can inherit every divisor common to the two `U` coefficients and every divisor common to the two `V` coefficients. Local copy of ErdosProblems.Erdos1049.rationalPadeExteriorDet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeExteriorDet (Un Vn Um Vm : ℤ) : ℤ :=
  Un * Vm - Um * Vn
end PalomarCorpus.E1049.PaperStatementsN
