/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band f

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Set
open Filter
open MeasureTheory
open scoped Topology

namespace PalomarCorpus.E1041.PaperStatementsF
open Set
open Filter
open MeasureTheory
open scoped Topology
/-- `coth t = cosh t / sinh t`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.coth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t
/-- The integrand `1 / log (coth t)` of the paper's `Φ`, carrying the paper's continuous limiting value `0` at `t = 0`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def orliczKernel (t : ℝ) : ℝ := 1 / Real.log (coth t)
/-- `Φ(x) = ∫_0^x dt / log (coth t)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Phi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, orliczKernel t
/-- `I_k(r) = ∫_r^1 dq / (q * log ((1 + q ^ (2/k)) / (1 - q ^ (2/k))))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mergerIntegral (k : ℕ) (r : ℝ) : ℝ :=
  ∫ q in r..(1 : ℝ),
    1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k))))
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_continuous : Continuous orliczKernel := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ)) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsF
