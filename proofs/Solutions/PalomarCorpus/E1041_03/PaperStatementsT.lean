/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole
import ErdosProblems.Erdos1041.PaperCurveAssembly
import Solutions.PalomarCorpus.E1041_03.Statement

open Polynomial
open Finset
open Set
open scoped NNReal
open scoped ENNReal

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsT

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

end PalomarCorpus.E1041.PaperStatementsT
