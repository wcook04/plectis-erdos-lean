/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, record section 2.6: proofs, earlier work and limitations

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open Filter
open Asymptotics
open scoped Topology
open Filter Asymptotics
open Polynomial
open scoped BigOperators
open Finset

namespace PalomarCorpus.E1049_02.Shared
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.maxCoeffNat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def maxCoeffNat (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.maxPairHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def maxPairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  (max (maxCoeffNat (U n)) (maxCoeffNat (V n)) : ℕ)
end PalomarCorpus.E1049_02.Shared

namespace PalomarCorpus.E1049.PaperStructuresD
open Filter
open Asymptotics
open scoped Topology
export PalomarCorpus.E1049_02.Shared (maxCoeffNat maxPairHeight)
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.pairWidth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairWidth (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ :=
  max (U n).natDegree (V n).natDegree
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.polynomialRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialRemainder (U V : ℕ → Polynomial ℤ)
    (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x -
    (V n).eval₂ (Int.castRingHom ℝ) x
/-- The scale is a real square, avoiding truncated natural subtraction. Local copy of ErdosProblems.Erdos1049.PaperR9.sqScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sqScale (n : ℕ) : ℝ := (n : ℝ) ^ 2
/-- Upper quadratic rate, with an arbitrary additive epsilon in the rate. Local copy of ErdosProblems.Erdos1049.PaperR9.QuadUpper, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuadUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ (a + ε) * sqScale n
/-- Exact two-sided logarithmic asymptotic; nonvanishing is supplied separately. Local copy of ErdosProblems.Erdos1049.PaperR9.QuadLogRate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuadLogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => Real.log |f n| - a * sqScale n) =o[atTop] sqScale
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.LongCapHypotheses, restated so the compared statements elaborate against Mathlib alone. -/
structure LongCapHypotheses (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  height_nonneg : 0 ≤ h
  degree_upper : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ
  height_upper : QuadUpper (fun n => Real.log (maxPairHeight U V n)) h
  nonzero : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, polynomialRemainder U V F x n ≠ 0
  remainder_rate : ∀ x : ℝ, 1 < x →
    QuadLogRate (polynomialRemainder U V F x) (-σ * Real.log x)
/-- States long1049:res:archcap from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR9.long_record_archcap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem long_record_archcap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h) :
    σ ≤ δ ∧ σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Filter.limsup (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop ≤
        δ * Real.log b - σ * Real.log ((a : ℝ) / b)) ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
        Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
    (∀ d : ℝ,
      Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d) →
        σ ≤ d ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          Tendsto (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
            polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop
            (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b)))) ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          (Real.log b / Real.log a < σ / (σ + d) →
            Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
          (σ / (σ + d) < Real.log b / Real.log a →
            Tendsto (fun n => |(b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n|) atTop atTop)) ∧
        Tendsto (fun n => |(2 : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((3 : ℝ) / 2) n|) atTop atTop) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresD

namespace PalomarCorpus.E1049.ArchimedeanCap
open Filter Asymptotics
open scoped Topology
/-- The declared clearing width of the n-th approximation pair: the larger of the degrees of the polynomials U n and V n, as a natural number. Under the Mathlib convention the zero polynomial has degree zero. -/
noncomputable def width (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ := max (U n).natDegree (V n).natDegree
/-- The remainder U_n(x) F(x) - V_n(x) of the n-th pair at the real point x, the polynomials being evaluated through the canonical ring map from the integers to the reals. Here F is an arbitrary real function supplied as a parameter rather than a fixed Lambert series. -/
noncomputable def remainder (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x - (V n).eval₂ (Int.castRingHom ℝ) x
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

namespace PalomarCorpus.E1049.PaperStructuresQ
open Filter
open Polynomial
open scoped BigOperators
open Finset
open Asymptotics
open scoped Topology
export PalomarCorpus.E1049_02.Shared (maxCoeffNat maxPairHeight)
/-- Local definition sourceAExponent, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceAExponent (n s : ℕ) : ℕ :=
  2 * n ^ 2 + (n + 1) * s + s.choose 2
/-- Local definition gaussBinom, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0
/-- Local definition sourceGaussianProduct, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceGaussianProduct (n s : ℕ) : ℤ[X] :=
  gaussBinom X (14 * n + s) (12 * n) *
    gaussBinom X (13 * n) (13 * n - s)
/-- Local definition sourceM, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceM (n : ℕ) : ℕ := 266 * n ^ 2 + 34 * n + 1
/-- Local definition sourceASummand, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ (sourceM n + sourceAExponent n s) *
    sourceGaussianProduct n s
/-- Local definition sourceNormalisedASummand, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceNormalisedASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ sourceAExponent n s * sourceGaussianProduct n s
/-- Local definition sourceAWithoutMonomial, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceAWithoutMonomial (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceNormalisedASummand n s
/-- Local copy of ErdosProblems.Erdos1049.PaperR7.omegaWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))
/-- Local definition sourceWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceWeight (n l : ℕ) : ℤ :=
  omegaWeight ((n : ℝ) / (l : ℝ))
/-- Local definition sourceComplement, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceComplement (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n),
    if sourceWeight n l = 0 then cyclotomic l ℤ else 1
/-- Local definition sourceOmega, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceOmega (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), (cyclotomic l ℤ) ^ (sourceWeight n l).toNat
/-- Local definition sourceU, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceU (n : ℕ) : ℤ[X] :=
  sourceComplement n * sourceAWithoutMonomial n
/-- Local definition sourceShiftedASummand, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceShiftedASummand (n s j : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) *
    X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s)) *
    sourceGaussianProduct n s
/-- Local definition sourceDQuotient, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceDQuotient (n j : ℕ) : ℤ[X] :=
  ∏ l ∈ (Finset.Icc 1 (15 * n) \ j.divisors), cyclotomic l ℤ
/-- Local definition sourceClearedB, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceClearedB (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1),
    ((∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j))
/-- Local definition sourceBWithoutMonomial, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceBWithoutMonomial (n : ℕ) : ℤ[X] :=
  sourceClearedB n /ₘ ((X : ℤ[X]) ^ sourceM n)
/-- Local definition sourceV, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def sourceV (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n /ₘ sourceOmega n
/-- States long1049:res:sourceheight from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.exists_quadratic_source_height_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (maxCoeffNat (sourceU n))
            (maxCoeffNat (sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2 := by
  sorry
/-- States long1049:res:sourceheight from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.maxPairHeight_source_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem maxPairHeight_source_eq (n : ℕ) :
    maxPairHeight sourceU sourceV n =
      ((max (maxCoeffNat (sourceU n))
        (maxCoeffNat (sourceV n)) : ℕ) : ℝ) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresQ
