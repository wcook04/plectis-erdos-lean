/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `6917e15ec4abc2623512254da93221e446eeb707` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.ActualMomentGeneratingR12`,
`ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation`,
`ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisationAnalytic`,
`ErdosProblems.Erdos1049.QBinomialUnitIdentity`,
`ErdosProblems.Erdos1049.QProductBoundsR10`.
-/

open PowerSeries
open Finset
open Filter
open scoped Topology
open scoped PowerSeries.WithPiTopology
open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStructuresAA

noncomputable abbrev BW := PowerSeries (PowerSeries ℚ)

noncomputable def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2

noncomputable def qPochhammer {R : Type*} [CommRing R] (q z : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q z n * (1 - z * q ^ n)

noncomputable abbrev qq : PowerSeries ℚ := PowerSeries.X

noncomputable def qfac (n : ℕ) : PowerSeries ℚ := qPochhammer qq qq n

noncomputable def qPochInf (x : BW) : BW := ∏' i : ℕ, (1 - x * C (qq ^ i))

noncomputable abbrev ww : BW := PowerSeries.X

noncomputable def momentGenFun : BW :=
  Ring.inverse (qPochInf ww ^ 3) *
    ∑' t : ℕ, ww ^ t * C (qfac t)⁻¹ *
      (qPochInf (C (qq ^ t) * ww ^ 2) * Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2))

noncomputable def momentWeight (k : ℕ) : PowerSeries ℚ := coeff k momentGenFun

noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

noncomputable def realRogersR (r k : ℕ) (q : ℝ) : ℝ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qPochhammerFinite q q k / ∏ j, qPochhammerFinite q q (n j)

noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

noncomputable def rogersPoly2 (k : ℕ) : Polynomial ℤ := ∑ i ∈ range (k + 1), gaussBinom Polynomial.X k i

noncomputable def rogersPoly3 (k : ℕ) : Polynomial ℤ :=
  ∑ p ∈ antidiagonal k, ∑ q ∈ antidiagonal p.2,
    gaussBinom Polynomial.X k p.1 * gaussBinom Polynomial.X p.2 q.1

noncomputable def rogersR (r k : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qfac k * (∏ j, qfac (n j))⁻¹

noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))

noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2

noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3

/-- States long1049:prop:rogers-factorisation from the long record for Erdős problem #1049.
Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem rogers_factorisation_proposition :
    (∀ k : ℕ,
      momentWeight k = rogersR 2 k * rogersR 3 k * (qfac k)⁻¹ ∧
      qfac k * momentWeight k = rogersR 2 k * rogersR 3 k ∧
      (∃ p : Polynomial ℕ,
        ((p.map (Nat.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
          rogersR 2 k * rogersR 3 k ∧
        p.natDegree = k ^ 2 / 4 + k ^ 2 / 3 ∧
        p.eval 1 = 6 ^ k) ∧
      (∃ g : Polynomial ℤ,
        qfac k * momentWeight k =
          ((g.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ))) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      (∀ w : ℝ, 0 ≤ w → w < 1 →
        HasSum (fun k => realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k * w ^ k)
          (actualGeneratingFunction q w)) ∧
      ∀ γ : ℕ → ℝ, (∀ w : ℝ, 0 ≤ w → w < 1 →
          HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) →
        (∀ k, γ k = realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k) ∧
        (∀ k, HasSum (fun m => ((coeff m (momentWeight k) : ℚ) : ℝ) * q ^ m) (γ k)) ∧
        (∀ k, realRogersR 2 k q = (rogersPoly2 k).eval₂ (Int.castRingHom ℝ) q ∧
          realRogersR 3 k q = (rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q ∧
          qPochhammerFinite q q k * γ k =
            (rogersPoly2 k * rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q) ∧
        (∀ k, qPochhammerInfinity q q ^ 5 * cK k ≤ qPochhammerInfinity q q ^ 4 * γ k ∧
          qPochhammerInfinity q q ^ 4 * γ k ≤ (qPochhammerInfinity q q)⁻¹ * cK k) ∧
        (∀ k h : ℕ, qPochhammerInfinity q q ^ 4 * γ (k + h) / (qPochhammerInfinity q q ^ 4 * γ k)
          ≤ ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3) ∧
        (∀ k, 0 < qPochhammerInfinity q q ^ 4 * γ k) ∧
        (∀ h : ℕ, Tendsto (fun k => qPochhammerInfinity q q ^ 4 * γ (k + h) /
          (qPochhammerInfinity q q ^ 4 * γ k)) atTop (𝓝 1))) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStructuresAA
