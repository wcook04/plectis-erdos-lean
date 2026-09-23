/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperCompleteR20.CriticalMeanWhole
import Solutions.PalomarCorpus.E1041_04.Statement

open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsO
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)

theorem critical_value_three_budgets {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) :
    (∑ j, ‖f.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := @ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets n hn f hf hdeg h R hR hroots c hc

end PalomarCorpus.E1041.PaperStatementsO
