/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.ActualPositiveMeasureR16
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBaseShort
import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import ErdosProblems.Erdos1049.QProductBoundsR10

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `6917e15ec4abc2623512254da93221e446eeb707` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.ActualMomentGeneratingR12`,
`ErdosProblems.Erdos1049.ActualPositiveMeasureR16`,
`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase`,
`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBaseShort`,
`ErdosProblems.Erdos1049.PaperR16.LambertBasic`,
`ErdosProblems.Erdos1049.QProductBoundsR10`.
-/

open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology

namespace Erdos249257.ExternalVerification1049PaperStatementsU

noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N

noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))

noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)

noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t

noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)

noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)

noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n

theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := @ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists q hq0 hq1

end Erdos249257.ExternalVerification1049PaperStatementsU
