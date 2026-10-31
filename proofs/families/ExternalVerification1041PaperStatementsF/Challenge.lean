/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR21.MergerScaleOrlicz`.
-/

open Set
open Filter
open MeasureTheory
open scoped Topology

namespace Erdos249257.ExternalVerification1041PaperStatementsF

noncomputable def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t

noncomputable def orliczKernel (t : ℝ) : ℝ := 1 / Real.log (coth t)

noncomputable def Phi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, orliczKernel t

noncomputable def mergerIntegral (k : ℕ) (r : ℝ) : ℝ :=
  ∫ q in r..(1 : ℝ),
    1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k))))

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k) := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k) := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_continuous : Continuous orliczKernel := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem orlicz_currency :
    (Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧ orliczKernel 0 = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r ≤ 1 →
        mergerIntegral k r = k * Phi (Real.log (1 / r) / k)) ∧
      StrictMonoOn Phi (Ioi (0 : ℝ)) ∧
      MonotoneOn Phi (Ioi (0 : ℝ)) ∧
      StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi ∧
      Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, 0 < c → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        mergerIntegral k r < c * (Real.log (1 / r) / k)) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r < 1 →
        c * (Real.log (1 / r) / k) ≤ mergerIntegral k r := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi := by
  sorry

/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ)) := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsF
