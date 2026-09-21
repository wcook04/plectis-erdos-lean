/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041o

Every non-theorem declaration of `PalomarCorpus/E1041o/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate

namespace PalomarCorpus.E1041.PaperStatementsO
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalEnumeration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootsInClosedDisc, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
end PalomarCorpus.E1041.PaperStatementsO
