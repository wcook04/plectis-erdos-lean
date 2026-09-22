/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band d

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Asymptotics
open scoped Topology

namespace PalomarCorpus.E1049.PaperStructuresD
open Filter
open Asymptotics
open scoped Topology
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.maxCoeffNat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def maxCoeffNat (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.maxPairHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def maxPairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  (max (maxCoeffNat (U n)) (maxCoeffNat (V n)) : ℕ)
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
