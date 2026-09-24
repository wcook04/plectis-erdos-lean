/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation
import ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisationAnalytic
import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import ErdosProblems.Erdos1049.QProductBoundsR10

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

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are elaborated here and recorded as derived transport in the
entry metadata. The bridges for `qPochhammer`, `qPochInf`, `momentGenFun`,
`momentWeight` and `gaussBinom` are written by hand; the others are generated.
-/

/-- The local copy of `ErdosProblems.Erdos1049.qPochhammer` is the same function: both
recursions give `1` at `0` and multiply by the same factor at each step. -/
theorem qPochhammer_transport_def : @qPochhammer = @ErdosProblems.Erdos1049.qPochhammer := by
  funext R _ q z n
  induction n with
  | zero => rfl
  | succ n ih => simp only [qPochhammer, ErdosProblems.Erdos1049.qPochhammer, ih]

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac` is the same function. -/
theorem qfac_transport_def : @qfac = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac := by
  first
  | (rfl; done)
  | (simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold qfac ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac; done)
  | (unfold qfac ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (ext x; simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a; fun_induction qfac a <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a; induction a <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a; induction a <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a; induction a <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a; simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a b; fun_induction qfac a b <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b; simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (funext a b c; fun_induction qfac a b c <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def, *]; done)
  | (funext a b c; simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)
  | (simp [qfac, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qfac, qPochhammer_transport_def]; done)

/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qPochInf` is the same function. -/
theorem qPochInf_transport_def : @qPochInf = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.qPochInf := rfl

/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentGenFun` is the same series: its two recursive ingredients are
replaced by their sources, and what remains agrees by unfolding. -/
theorem momentGenFun_transport_def : @momentGenFun = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentGenFun := by
  unfold momentGenFun ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentGenFun
  rw [qfac_transport_def, qPochInf_transport_def]

/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentWeight` is the same function. -/
theorem momentWeight_transport_def : @momentWeight = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentWeight := by
  funext k
  unfold momentWeight ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.momentWeight
  rw [momentGenFun_transport_def]

/-- The local copy of `ErdosProblems.Erdos1049.gaussBinom` is the same function: both are the
same Pascal recursion, compared case by case. -/
theorem gaussBinom_transport_def : @gaussBinom = @ErdosProblems.Erdos1049.gaussBinom := by
  funext R _ q n k
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, ih]

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2` is the same function. -/
theorem rogersPoly2_transport_def : @rogersPoly2 = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2 := by
  first
  | (rfl; done)
  | (simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold rogersPoly2 ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2; done)
  | (unfold rogersPoly2 ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2 <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (ext x; simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a; fun_induction rogersPoly2 a <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a; simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a b; fun_induction rogersPoly2 a b <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b; simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (funext a b c; fun_induction rogersPoly2 a b c <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, *]; done)
  | (funext a b c; simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)
  | (simp [rogersPoly2, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly2, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3` is the same function. -/
theorem rogersPoly3_transport_def : @rogersPoly3 = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3 := by
  first
  | (rfl; done)
  | (simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold rogersPoly3 ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3; done)
  | (unfold rogersPoly3 ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3 <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (ext x; simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a; fun_induction rogersPoly3 a <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a; induction a <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a; simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a b; fun_induction rogersPoly3 a b <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b; simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (funext a b c; fun_induction rogersPoly3 a b c <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, *]; done)
  | (funext a b c; simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)
  | (simp [rogersPoly3, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersPoly3, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR` is the same function. -/
theorem rogersR_transport_def : @rogersR = @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR := by
  first
  | (rfl; done)
  | (simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold rogersR ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR; done)
  | (unfold rogersR ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (ext x; simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a; fun_induction rogersR a <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a; induction a <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a; induction a <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a; simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a b; fun_induction rogersR a b <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b; simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (funext a b c; fun_induction rogersR a b c <;> simp only [ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, *]; done)
  | (funext a b c; simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)
  | (simp [rogersR, ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogersR, qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def]; done)

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
  simp only [qPochhammer_transport_def, qfac_transport_def, momentGenFun_transport_def, momentWeight_transport_def, gaussBinom_transport_def, rogersPoly2_transport_def, rogersPoly3_transport_def, rogersR_transport_def]
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition

end Erdos249257.ExternalVerification1049PaperStructuresAA
