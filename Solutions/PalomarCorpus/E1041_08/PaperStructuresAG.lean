/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.Counterexample.Defs
import ErdosProblems.Erdos1041.Counterexample.HausdorffLength
import Solutions.PalomarCorpus.E1041_08.Statement

open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStructuresAG

noncomputable def A : ℚ := -5 + 12 * t - 3 * t ^ 2

noncomputable def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)

noncomputable def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I

noncomputable def c : ℂ := -(Cconst : ℂ) - (162 / 25 : ℚ) * (s : ℂ) * Complex.I

noncomputable def ε : ℚ := s ^ 2

noncomputable def ρ : ℚ := 1 - s ^ 16

noncomputable def f : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ρ : ℂ) * (ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ρ : ℂ) ^ 2 * (ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ρ : ℂ) ^ 3 * (ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-(ρ : ℂ) ^ 7)

theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by
  first
  | (exact @Erdos1041.Counterexample.erdos1041_counterexample_hausdorff; done)
  | (set_option smartUnfolding false in
      exact @Erdos1041.Counterexample.erdos1041_counterexample_hausdorff; done)
  | (apply Erdos1041.Counterexample.erdos1041_counterexample_hausdorff <;> assumption; done)
  | (simpa only [A, B, Cconst, Omega, a, b, c, f, s, shiftQuad, t, ε, ρ] using Erdos1041.Counterexample.erdos1041_counterexample_hausdorff; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos1041.Counterexample.erdos1041_counterexample_hausdorff; done)
  | (with_unfolding_all exact @Erdos1041.Counterexample.erdos1041_counterexample_hausdorff; done)

theorem s3_bottleneck_hausdorff
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ μH[1] K := by
  first
  | (exact @Erdos1041.Counterexample.s3_bottleneck_hausdorff p cc hcc hcrit hv b₁ b₂ hne hb₁ hb₂ hr₁ hr₂ hzeros huniq aHat haHat h hh hdisk δ hδ hδpos hδsmall K hK hKsub hK₁ hK₂; done)
  | (set_option smartUnfolding false in
      exact @Erdos1041.Counterexample.s3_bottleneck_hausdorff p cc hcc hcrit hv b₁ b₂ hne hb₁ hb₂ hr₁ hr₂ hzeros huniq aHat haHat h hh hdisk δ hδ hδpos hδsmall K hK hKsub hK₁ hK₂; done)
  | (apply Erdos1041.Counterexample.s3_bottleneck_hausdorff <;> assumption; done)
  | (simpa only [A, B, Cconst, Omega, a, b, c, f, s, shiftQuad, t, ε, ρ] using Erdos1041.Counterexample.s3_bottleneck_hausdorff; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @Erdos1041.Counterexample.s3_bottleneck_hausdorff p cc hcc hcrit hv b₁ b₂ hne hb₁ hb₂ hr₁ hr₂ hzeros huniq aHat haHat h hh hdisk δ hδ hδpos hδsmall K hK hKsub hK₁ hK₂; done)
  | (with_unfolding_all exact @Erdos1041.Counterexample.s3_bottleneck_hausdorff p cc hcc hcrit hv b₁ b₂ hne hb₁ hb₂ hr₁ hr₂ hzeros huniq aHat haHat h hh hdisk δ hδ hδpos hδsmall K hK hKsub hK₁ hK₂; done)

end PalomarCorpus.E1041.PaperStructuresAG
