/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole
import ErdosProblems.Erdos1041.PaperCurveAssembly

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole`,
`ErdosProblems.Erdos1041.PaperCurveAssembly`.
-/

open Polynomial
open Finset
open Set
open scoped NNReal
open scoped ENNReal

namespace Erdos249257.ExternalVerification1041PaperStatementsT

noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L

theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := @ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041 n hn base dir hdir y f hf hdisc

theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ConnectedBelow f.eval 1 2 a b := @ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041_monic n hn f hf base dir hdir hcol hdisc

end Erdos249257.ExternalVerification1041PaperStatementsT
