/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality
import ErdosProblems.Erdos1049.QProductBoundsR10

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `6917e15ec4abc2623512254da93221e446eeb707` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality`,
`ErdosProblems.Erdos1049.QProductBoundsR10`.
-/

open Filter
open Finset
open Matrix
open scoped Topology
open scoped BigOperators
open scoped Classical

namespace Erdos249257.ExternalVerification1049PaperStructuresW

noncomputable def geomMoment (q : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, a k * q ^ ((m + 1) * k)

noncomputable def geomHankelDet (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin N => geomMoment q a (i.val + j.val)).det

noncomputable def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹

noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))

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
  apply ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality <;> assumption

end Erdos249257.ExternalVerification1049PaperStructuresW
