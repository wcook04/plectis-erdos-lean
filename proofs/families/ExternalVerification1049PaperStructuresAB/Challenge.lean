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
`ErdosProblems.Erdos1049.ActualPositiveMeasureR16`,
`ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality`,
`ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisationAnalytic`,
`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase`,
`ErdosProblems.Erdos1049.QProductBoundsR10`.
-/

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Matrix
open scoped Classical
open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Erdos249257.ExternalVerification1049PaperStructuresAB

noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹

noncomputable def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2

noncomputable def lambertL (q : ℝ) : ℝ := ∑' r : ℕ, q ^ (r + 1) / (1 - q ^ (r + 1))

noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N

noncomputable def orderB (N : ℕ) : ℕ := ∑ j ∈ range N, j ^ 2

noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))

noncomputable def sharpFactor (q : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  qPochhammerInfinity q q ^ 4 * γ k / cK k * Real.exp (8 * lambertL q / ((k : ℝ) + 1))

noncomputable def sharpA (q : ℝ) (γ : ℕ → ℝ) : ℝ :=
  Real.exp (-8 * Real.eulerMascheroniConstant * lambertL q) * ∏' k : ℕ, sharpFactor q γ k

noncomputable def sharpK (q : ℝ) (γ : ℕ → ℝ) : ℝ := sharpA q γ * gramM q ^ 3

noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2

noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3

noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)

noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t

noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)

/-- States long1049:thm:sharp-fixed-base from the long record for Erdős problem #1049.
Transported from ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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

end Erdos249257.ExternalVerification1049PaperStructuresAB
