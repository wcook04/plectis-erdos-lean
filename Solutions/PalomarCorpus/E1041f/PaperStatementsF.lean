/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.MergerScaleOrlicz
import Solutions.PalomarCorpus.E1041f.Statement

open Set
open Filter
open MeasureTheory
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsF

theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k) := @ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt k hk c hc

theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k) := @ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi k hk r hr0 hr1

theorem orliczKernel_continuous : Continuous orliczKernel := @ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous

theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) := @ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero

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
        c * (Real.log (1 / r) / k) ≤ mergerIntegral k r := @ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency

theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := @ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero

theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi := @ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn

theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ)) := @ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn

end PalomarCorpus.E1041.PaperStatementsF
