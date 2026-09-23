/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCubicCompletion
import ErdosProblems.Erdos1041.PaperCubicMonic
import Solutions.PalomarCorpus.E1041_02.Statement

open Polynomial Set
open scoped BigOperators

namespace PalomarCorpus.E1041.CubicPath

noncomputable section

theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by
  simpa only [hub, ErdosProblems.Erdos1041.PaperCurve.hub,
    ErdosProblems.Erdos1041.PaperCurve.HubBelow,
    ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow] using
    (ErdosProblems.Erdos1041.PaperCubicCompletion.cubic_paper_complete p z hp hz)

theorem monic_cubic_connector (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1) :
    ∃ a b c : ℂ, p.eval a = 0 ∧ p.eval b = 0 ∧
      Continuous (hub a c b) ∧
      BoundedVariationOn (hub a c b) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub a c b t)‖ < 1) ∧
        eVariationOn (hub a c b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = a ∧ γ 2 = b ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → a ≠ b) := by
  simpa only [hub, ErdosProblems.Erdos1041.PaperCurve.hub,
    ErdosProblems.Erdos1041.PaperCurve.HubBelow,
    ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow] using
    (ErdosProblems.Erdos1041.PaperCubicMonic.monic_cubic_connector p hm hd hz)

theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖P.eval ((hub a h b t - h) ^ q)‖ < 1) ∧
      eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2 := by
  simpa only [hub, ErdosProblems.Erdos1041.PaperCurve.hub,
    ErdosProblems.Erdos1041.PaperCurve.HubBelow] using
    (ErdosProblems.Erdos1041.PaperCubicFibres.complete_translated_cubic_quotient_fibres
      hq h P hP hdeg hdisk htwo)

end

end PalomarCorpus.E1041.CubicPath
