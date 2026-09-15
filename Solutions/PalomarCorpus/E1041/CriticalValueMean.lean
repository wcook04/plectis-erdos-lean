/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCriticalValueMeanR10
import Solutions.PalomarCorpus.E1041.Statement

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E1041.CriticalValueMean

theorem paper_critical_value_mean (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ)
    (hn : 2 ≤ n) (hp : p.Monic) (hdeg : p.natDegree = n) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R :=
  ErdosProblems.Erdos1041.paper_critical_value_mean n p c h R hn hp hdeg hR hroots hc

end PalomarCorpus.E1041.CriticalValueMean
