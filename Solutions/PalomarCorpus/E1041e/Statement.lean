/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041e

Every non-theorem declaration of `PalomarCorpus/E1041e/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open Finset
open Set

namespace PalomarCorpus.E1041.PaperStatementsE
open Polynomial
open Finset
open Set
/-- The conclusion of the sharp collinear diameter theorem, with the constant left as a parameter `K`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CollinearDiameterBound (n : ℕ) (K : ℝ) : Prop :=
  ∀ base dir : ℂ, ‖dir‖ = 1 → ∀ (y : Fin n → ℝ) (f : ℂ[X]),
    f = (∏ k, (X - C (base + dir * (y k : ℂ)))) → ∀ D : ℝ,
      IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ K * (D / 2) ^ n
end PalomarCorpus.E1041.PaperStatementsE
