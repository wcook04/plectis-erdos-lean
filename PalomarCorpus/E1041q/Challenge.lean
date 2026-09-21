/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band q

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Set
open Metric
open AffineSubspace
open Polynomial

namespace PalomarCorpus.E1041.PaperStatementsQ
open Set
open Metric
open AffineSubspace
open Polynomial
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.P, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def P : ℂ[X] := X ^ 3 + (C (3 / 100 : ℂ) * X ^ 1 + C (-3 / 4 : ℂ))
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.minus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def minus : ℂ := -Complex.I / 10
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.plus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def plus : ℂ := Complex.I / 10
/-- Local copy of ErdosProblems.Erdos1041.PaperSeparationCounterexample.mu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mu : ℝ := ‖P.eval plus‖
/-- Two complex values lie on the same oriented ray from the origin. Local copy of ErdosProblems.Erdos1041.SamePositiveRay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a
/-- The complex Newton vector associated with a value and its nonzero derivative. Local copy of ErdosProblems.Erdos1041.newtonFlowVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def newtonFlowVector (value derivative : ℂ) : ℂ :=
  -value / derivative
/-- States res:ray from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem newton_real_endpoint_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hc : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) ∧
      SamePositiveRay (f (z a)) (f (z b)) := by
  sorry
/-- States res:value from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem newton_real_value_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ I,
      HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : ∀ t ∈ I, f' (z t) ≠ 0) :
    (∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t) ∧
    (∀ t ∈ I, ∀ t₀ ∈ I,
      f (z t) = (Real.exp (-(t - t₀)) : ℂ) * f (z t₀)) := by
  sorry
/-- States res:sep-or-false from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
    (2 / 375 : ℝ) < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsQ
