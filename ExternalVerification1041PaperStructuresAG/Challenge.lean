/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.Counterexample.Defs`,
`ErdosProblems.Erdos1041.Counterexample.HausdorffLength`.
-/

open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate

namespace Erdos249257.ExternalVerification1041PaperStructuresAG

noncomputable def t : ℚ := 417 / 40

noncomputable def A : ℚ := -5 + 12 * t - 3 * t ^ 2

noncomputable def B : ℚ := -4 + 4 * t + 6 * t ^ 2

noncomputable def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)

noncomputable def Omega (p : Polynomial ℂ) : Set ℂ := {z : ℂ | ‖p.eval z‖ < 1}

noncomputable def s : ℚ := 1 / 10 ^ 6

noncomputable def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I

noncomputable def b : ℂ := Complex.I * (B : ℂ) + (9 / 5 : ℚ) * (s : ℂ)

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

noncomputable def shiftQuad (p : Polynomial ℂ) (cc : ℂ) : Polynomial ℂ :=
  (p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)) /ₘ
    (Polynomial.X ^ 2)

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from
the long record and the short record for Erdős problem #1041. Transported from
Erdos1041.Counterexample.erdos1041_counterexample_hausdorff in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by
  sorry

/-- States lem:two-sheet-bottleneck, lem:two-sheet-bottleneck-long from the long record and the
short record for Erdős problem #1041. Transported from
Erdos1041.Counterexample.s3_bottleneck_hausdorff in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
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
  sorry

end Erdos249257.ExternalVerification1041PaperStructuresAG
