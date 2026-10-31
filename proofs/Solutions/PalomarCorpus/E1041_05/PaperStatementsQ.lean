/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import ErdosProblems.Erdos1041.PaperCompleteR20.NewtonRealTime
import ErdosProblems.Erdos1041.PaperSeparationCounterexample
import Solutions.PalomarCorpus.E1041_05.Statement

open Set
open Metric
open AffineSubspace
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsQ

noncomputable def newtonFlowVector (value derivative : ℂ) : ℂ :=
  -value / derivative

theorem newton_real_endpoint_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hc : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) ∧
      SamePositiveRay (f (z a)) (f (z b)) := @ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole f f' z a b hab hcont hf hz hc

theorem newton_real_value_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ I,
      HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : ∀ t ∈ I, f' (z t) ≠ 0) :
    (∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t) ∧
    (∀ t ∈ I, ∀ t₀ ∈ I,
      f (z t) = (Real.exp (-(t - t₀)) : ℂ) * f (z t₀)) := @ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole f f' z I hI hf hz hc

theorem complete_sep_or_counterexample :
    P.Monic ∧ P.natDegree = 3 ∧
    (∀ z : ℂ, P.eval z = 0 → ‖z‖ < 1) ∧
    (∀ z : ℂ, P.derivative.eval z = 0 ↔ z = plus ∨ z = minus) ∧
    plus ≠ minus ∧
    (∀ z : ℂ, P.derivative.eval z = 0 → P.derivative.derivative.eval z ≠ 0) ∧
    IsLeast {x : ℝ | ∃ c : ℂ, P.derivative.eval c = 0 ∧ x = ‖P.eval c‖} mu ∧
    (13 / 25 : ℝ) < mu ∧
    ¬ SamePositiveRay (P.eval plus) (P.eval minus) ∧
    ‖1 - P.eval minus / P.eval plus‖ < (2 / 375 : ℝ) ∧
    (2 / 375 : ℝ) < 2 := @ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample

end PalomarCorpus.E1041.PaperStatementsQ
