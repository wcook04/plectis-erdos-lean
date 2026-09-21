/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041q

Every non-theorem declaration of `PalomarCorpus/E1041q/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1041.PaperStatementsQ
