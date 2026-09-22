/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049d

Every non-theorem declaration of `PalomarCorpus/E1049d/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1049.PaperStructuresD
