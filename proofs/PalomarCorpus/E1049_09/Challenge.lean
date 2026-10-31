/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, the paper structures AA, paper structures AB and paper structures v families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open PowerSeries
open Finset
open Filter
open scoped Topology
open scoped PowerSeries.WithPiTopology
open scoped BigOperators
open Matrix
open scoped Classical

namespace PalomarCorpus.E1049_09.Shared
/-- Local definition cK, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2
/-- Local definition gramM, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹
/-- Local definition qPochhammerFinite, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
/-- Local definition qPochhammerInfinity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
/-- Local definition actualGeneratingTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2
/-- Local definition actualGeneratingFunction, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3
end PalomarCorpus.E1049_09.Shared

namespace PalomarCorpus.E1049.PaperStructuresAA
open PowerSeries
open Finset
open Filter
open scoped Topology
open scoped PowerSeries.WithPiTopology
open scoped BigOperators
export PalomarCorpus.E1049_09.Shared (actualGeneratingFunction actualGeneratingTerm cK qPochhammerFinite qPochhammerInfinity)
/-- Local definition BW, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev BW := PowerSeries (PowerSeries ℚ)
/-- Local definition qPochhammer, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammer {R : Type*} [CommRing R] (q z : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q z n * (1 - z * q ^ n)
/-- Local definition qq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev qq : PowerSeries ℚ := PowerSeries.X
/-- Local definition qfac, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qfac (n : ℕ) : PowerSeries ℚ := qPochhammer qq qq n
/-- Local definition qPochInf, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochInf (x : BW) : BW := ∏' i : ℕ, (1 - x * C (qq ^ i))
/-- Local definition ww, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev ww : BW := PowerSeries.X
/-- Local definition momentGenFun, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def momentGenFun : BW :=
  Ring.inverse (qPochInf ww ^ 3) *
    ∑' t : ℕ, ww ^ t * C (qfac t)⁻¹ *
      (qPochInf (C (qq ^ t) * ww ^ 2) * Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2))
/-- Local definition momentWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def momentWeight (k : ℕ) : PowerSeries ℚ := coeff k momentGenFun
/-- Local definition realRogersR, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def realRogersR (r k : ℕ) (q : ℝ) : ℝ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qPochhammerFinite q q k / ∏ j, qPochhammerFinite q q (n j)
/-- Local definition gaussBinom, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0
/-- Local definition rogersPoly2, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersPoly2 (k : ℕ) : Polynomial ℤ := ∑ i ∈ range (k + 1), gaussBinom Polynomial.X k i
/-- Local definition rogersPoly3, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersPoly3 (k : ℕ) : Polynomial ℤ :=
  ∑ p ∈ antidiagonal k, ∑ q ∈ antidiagonal p.2,
    gaussBinom Polynomial.X k p.1 * gaussBinom Polynomial.X p.2 q.1
/-- Local definition rogersR, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rogersR (r k : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qfac k * (∏ j, qfac (n j))⁻¹
/-- States long1049:prop:rogers-factorisation from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
end PalomarCorpus.E1049.PaperStructuresAA

namespace PalomarCorpus.E1049.PaperStructuresAB
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology
export PalomarCorpus.E1049_09.Shared (actualGeneratingFunction actualGeneratingTerm cK gramM qPochhammerFinite qPochhammerInfinity)
/-- Local definition lambertL, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertL (q : ℝ) : ℝ := ∑' r : ℕ, q ^ (r + 1) / (1 - q ^ (r + 1))
/-- Local definition leadC, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- Local definition orderB, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def orderB (N : ℕ) : ℕ := ∑ j ∈ range N, j ^ 2
/-- Local definition sharpFactor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpFactor (q : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  qPochhammerInfinity q q ^ 4 * γ k / cK k * Real.exp (8 * lambertL q / ((k : ℝ) + 1))
/-- Local definition sharpA, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpA (q : ℝ) (γ : ℕ → ℝ) : ℝ :=
  Real.exp (-8 * Real.eulerMascheroniConstant * lambertL q) * ∏' k : ℕ, sharpFactor q γ k
/-- Local definition sharpK, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sharpK (q : ℝ) (γ : ℕ → ℝ) : ℝ := sharpA q γ * gramM q ^ 3
/-- Local definition actualMomentTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)
/-- Local definition actualMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t
/-- Local definition actualMomentHankel, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)
/-- States long1049:thm:sharp-fixed-base from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sharp_fixed_base {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (γ : ℕ → ℝ)
    (hγ : ∀ w : ℝ, 0 ≤ w → w < 1 →
      HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) :
    HasProd (sharpFactor q γ) (∏' k : ℕ, sharpFactor q γ k) ∧
    0 < sharpA q γ ∧
    Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (sharpK q γ * leadC N * q ^ orderB N * qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => Real.log (actualMomentHankel q N).det -
        ((orderB N : ℝ) * Real.log q + Real.log (leadC N) +
          2 * (N : ℝ) * Real.log (qPochhammerInfinity q q) - 8 * lambertL q * Real.log N +
          Real.log (sharpK q γ))) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresAB

namespace PalomarCorpus.E1049.PaperStructuresV
open Finset
/-- Local definition rowModD, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def rowModD (D : ℕ) (v : ℤ × ℤ) : ZMod D × ZMod D := ((v.1 : ZMod D), (v.2 : ZMod D))
/-- Local definition tailPartialSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailPartialSum (a b m : ℕ) : ℚ :=
  ∑ r ∈ Icc 1 m, ((b : ℚ) / a) ^ r / (1 - ((b : ℚ) / a) ^ r)
/-- Local definition tailP, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailP (a b m : ℕ) : ℤ := (tailPartialSum a b m).num
/-- Local definition tailQ, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailQ (a b m : ℕ) : ℤ := ((tailPartialSum a b m).den : ℤ)
/-- Local definition tailMinor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailMinor (a b i j : ℕ) : ℤ := tailQ a b i * tailP a b j - tailP a b i * tailQ a b j
/-- Local definition tailRow, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailRow (a b m : ℕ) : ℤ × ℤ := (tailQ a b m, tailP a b m)
/-- Local definition tailPrefixLattice, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def tailPrefixLattice (a b M : ℕ) : Submodule ℤ (ℤ × ℤ) :=
  Submodule.span ℤ (tailRow a b '' Set.Iio M)
/-- States long1049:res:tail-lattice from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice.tail_prefix_lattice in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_prefix_lattice (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) (hab : Nat.Coprime a b) :
    (∀ m, 0 < tailQ a b m ∧ Int.gcd (tailQ a b m) (tailP a b m) = 1) ∧
    (∀ m, IsCoprime (tailQ a b m) ((a : ℤ) * b)) ∧
    (∀ m, (b : ℤ) ∣ tailP a b m) ∧
    (∀ M, 2 ≤ M →
      tailPrefixLattice a b M = (⊤ : Submodule ℤ ℤ).prod (Submodule.span ℤ {(b : ℤ)}) ∧
      (∃ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a = ![1, (b : ℤ)]) ∧
      (∀ n, Nonempty (Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) n) → n = 2) ∧
      (∀ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a 0 ∣ snf.a 1 → IsUnit (snf.a 0) ∧ Associated (snf.a 1) (b : ℤ)) ∧
      (Finset.univ : Finset (Fin M × Fin M)).gcd
          (fun ij => tailMinor a b ij.1 ij.2) = (b : ℤ) ∧
      (∀ D : ℕ, 1 ≤ D →
        (rowModD D '' (tailPrefixLattice a b M : Set (ℤ × ℤ))).ncard = D ^ 2 / Nat.gcd b D)) ∧
    (∀ m (w : ℚ), w ≠ 0 → ∀ (c : ℚ) (A B : ℤ), c ≠ 0 →
      (A : ℚ) = c * (w * tailQ a b m) → (B : ℚ) = c * (w * tailP a b m) →
      (∃ k : ℤ, k ≠ 0 ∧ (A, B) = k • tailRow a b m) ∧
      ((A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = tailRow a b m ∨
        (A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = -tailRow a b m)) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresV

namespace PalomarCorpus.E1049.PaperStructuresW
open Filter
open Finset
open Matrix
open scoped Topology
open scoped BigOperators
open scoped Classical
export PalomarCorpus.E1049_09.Shared (gramM qPochhammerInfinity)
/-- Local definition geomMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomMoment (q : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, a k * q ^ ((m + 1) * k)
/-- Local definition geomHankelDet, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def geomHankelDet (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin N => geomMoment q a (i.val + j.val)).det
/-- States long1049:thm:geometric-universality from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem geometric_universality {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C κ : ℝ}
    (hlim : ∀ h : ℕ, Tendsto (fun k => a (k + h) / a k) atTop (𝓝 1))
    (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ κ) :
    HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹) (gramM q) ∧ 0 < gramM q ∧
    (∀ m : ℕ, Summable fun k => a k * q ^ ((m + 1) * k)) ∧
    Tendsto (fun N : ℕ => geomHankelDet q a N /
        (gramM q ^ 3 * q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) *
          ∏ k ∈ range N, a k))
      atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresW
