/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `a25cb360bef8dd818dde14b5fb752244304af354` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperR16.LambertBasic`,
`ErdosProblems.Erdos1049.PaperR20.CoefficientPencil`,
`ErdosProblems.Erdos1049.PaperR20.FinitePencilProposition`,
`ErdosProblems.Erdos1049.QBinomialUnitIdentity`.
-/

open Matrix
open Polynomial
open scoped BigOperators
open Filter
open Topology
open Finset

namespace Erdos249257.ExternalVerification1049PaperStructuresO

noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)

noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n

noncomputable def coefficientQFactorialPoly (m : ℕ) : ℤ[X] :=
  ∏ j ∈ range m, ∑ i ∈ range (j + 1), X ^ i

noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

noncomputable def coefficientRPoly (m : ℕ) : ℤ[X] :=
  ∑ k ∈ range (m + 1),
    C ((-1 : ℤ) ^ (m + k)) * X ^ (k * (k + 1) / 2) *
      gaussBinom X m k * gaussBinom X (m + k) k

noncomputable def coefficientMomentPoly (m : ℕ) : ℤ[X] :=
  coefficientQFactorialPoly m ^ 3 * coefficientRPoly m

noncomputable def coefficientAlphaPoly (m : ℕ) : ℤ[X] :=
  X * (X * (X - 1) ^ 3) ^ m * coefficientMomentPoly m

noncomputable def coefficientAlpha (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientAlphaPoly m).eval₂ (Int.castRingHom ℝ) p

noncomputable def coefficientAlphaMatrix (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => coefficientAlpha p (i.val + j.val)

noncomputable def divisorCount (j : ℕ) : ℤ := (Nat.divisors j).card

noncomputable def lambertPolynomialPart (P : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ range (P.natDegree + 1),
    C (P.coeff i) * ∑ r ∈ range i, C (divisorCount (i - r)) * X ^ r

noncomputable def coefficientBetaPoly (m : ℕ) : ℤ[X] :=
  lambertPolynomialPart (coefficientAlphaPoly m) - 1

noncomputable def coefficientBeta (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientBetaPoly m).eval₂ (Int.castRingHom ℝ) p

noncomputable def coefficientPencilPoly (p : ℝ) (N : ℕ) : ℝ[X] :=
  Matrix.det (Matrix.of fun i j : Fin N =>
    X * C (coefficientAlpha p (i.val + j.val)) -
      C (coefficientBeta p (i.val + j.val)))

/-- States long1049:res:finite-pencil from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperR20.coefficientPencil_finitePencil in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coefficientPencil_finitePencil {p : ℝ} (hp : 1 < p) :
    (∀ N : ℕ, N ≤ 8 →
      (coefficientAlphaMatrix p N).PosDef ∧
        (coefficientPencilPoly p N).Splits ∧
        ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x → x < lambert (1 / p)) ∧
    (∀ N : ℕ, N + 1 ≤ 8 →
      ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
        Antitone large ∧ Antitone small ∧
        (coefficientPencilPoly p (N + 1)).roots = Multiset.map large Finset.univ.val ∧
        (coefficientPencilPoly p N).roots = Multiset.map small Finset.univ.val ∧
        ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStructuresO
