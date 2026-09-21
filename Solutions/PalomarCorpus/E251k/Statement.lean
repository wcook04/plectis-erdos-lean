/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251k

Every non-theorem declaration of `PalomarCorpus/E251k/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Finset
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsK
open Filter
open Topology
open Finset
open scoped BigOperators
/-- Asymptotic density zero, with no assumption of existence of a density. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.ZeroDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
end PalomarCorpus.E251.PaperStatementsK
